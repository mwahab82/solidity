/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsolidity/analysis/FunctionCallGraph.h>

using namespace std;
using namespace solidity::frontend;

namespace {

bool nodeSet(FunctionCallGraphBuilder::Node const& _node)
{
	if (auto node = std::get_if<FunctionCallGraphBuilder::SpecialNode>(&_node))
		return *node != FunctionCallGraphBuilder::SpecialNode::Unset;

	return true;
}

}

namespace solidity::frontend
{


shared_ptr<FunctionCallGraphBuilder::ContractCallGraph> const FunctionCallGraphBuilder::create(ContractDefinition const& _contract)
{
	m_contract = &_contract;

	m_graph = make_shared<ContractCallGraph>(_contract);

	// Create graph for constructor, state vars, etc
	m_currentNode = SpecialNode::CreationRoot;
	m_currentDispatch = SpecialNode::CreationDispatch;
	visitConstructor(
		_contract,
		_contract.annotation().linearizedBaseContracts.cbegin() + 1,
		_contract.annotation().linearizedBaseContracts.cend()
	);
	m_currentNode = SpecialNode::Unset;
	m_currentDispatch = SpecialNode::RuntimeDispatch;

	// Create graph for all publicly reachable functions
	for (auto& [hash, functionType]: _contract.interfaceFunctionList())
		if (auto const* funcDef = dynamic_cast<FunctionDefinition const*>(&functionType->declaration()))
			if (!m_graph->edges.count(funcDef))
				visitCallable(funcDef);

	// Add all CreationDispatch calls to the RuntimeDispatch as well
	for (auto node: m_graph->edges[SpecialNode::CreationDispatch])
		add(SpecialNode::RuntimeDispatch, node);

	// Add all external functions to the RuntimeDispatch
	for (auto& [hash, functionType]: _contract.interfaceFunctionList())
		add(SpecialNode::RuntimeDispatch, &functionType->declaration());

	if (_contract.fallbackFunction())
		add(SpecialNode::RuntimeDispatch, _contract.fallbackFunction());

	if (_contract.receiveFunction())
		add(SpecialNode::RuntimeDispatch, _contract.receiveFunction());

	m_contract = nullptr;
	solAssert(!nodeSet(m_currentNode), "Current node not properly reset.");

	return m_graph;
}

bool FunctionCallGraphBuilder::visit(Identifier const& _identifier)
{
	if (auto const* callable = dynamic_cast<CallableDeclaration const*>(_identifier.annotation().referencedDeclaration))
	{
		solAssert(*_identifier.annotation().requiredLookup == VirtualLookup::Virtual, "");

		auto funType = dynamic_cast<FunctionType const*>(_identifier.annotation().type);
		solAssert(funType->kind() == FunctionType::Kind::Internal, "");

		processFunction(callable->resolveVirtual(*m_contract), _identifier.annotation());

		solAssert(nodeSet(m_currentNode), "");
	}

	return true;
}

bool FunctionCallGraphBuilder::visit(NewExpression const& _newExpression)
{
	if (ContractType const* contractType = dynamic_cast<ContractType const*>(_newExpression.typeName().annotation().type))
		m_graph->createdContracts.emplace(&contractType->contractDefinition());

	return true;
}

bool FunctionCallGraphBuilder::visit(MemberAccess const& _memberAccess)
{
	// Bound functions
	if (auto funType = dynamic_cast<FunctionType const*>(_memberAccess.annotation().type))
		if (funType->bound() && funType->kind() == FunctionType::Kind::Internal)
		{
			processFunction(dynamic_cast<CallableDeclaration const&>(funType->declaration()), _memberAccess.annotation());
			return true;
		}

	// Direct access functions like C.foo()
	if (TypeType const* type = dynamic_cast<TypeType const*>(_memberAccess.expression().annotation().type))

		if (dynamic_cast<ContractType const*>(type->actualType()))
			if (auto funType = dynamic_cast<FunctionType const*>(_memberAccess.annotation().type))
				if (funType->kind() == FunctionType::Kind::Internal)
					if (auto const* function = dynamic_cast<FunctionDefinition const*>(_memberAccess.annotation().referencedDeclaration))
					{
						solAssert(*_memberAccess.annotation().requiredLookup == VirtualLookup::Static, "");
						processFunction(*function, _memberAccess.annotation());
						return true;
					}

	// Free functions referenced through modules
	if (_memberAccess.expression().annotation().type->category() == Type::Category::Module)
		if (auto const* function = dynamic_cast<FunctionDefinition const*>(_memberAccess.annotation().referencedDeclaration))
		{
			auto funType = dynamic_cast<FunctionType const*>(_memberAccess.annotation().type);
			solAssert(function && function->isFree(), "");
			solAssert(funType->kind() == FunctionType::Kind::Internal, "");
			solAssert(*_memberAccess.annotation().requiredLookup == VirtualLookup::Static, "");
			processFunction(*function, _memberAccess.annotation());
			return true;
		}

	// Super functions
	if (_memberAccess.expression().annotation().type->category() == Type::Category::Contract)
	{
		ContractType const& type = dynamic_cast<ContractType const&>(*_memberAccess.expression().annotation().type);
		if (type.isSuper())
		{
			solAssert(!!_memberAccess.annotation().referencedDeclaration, "Referenced declaration not resolved.");
			solAssert(*_memberAccess.annotation().requiredLookup == VirtualLookup::Super, "");

			auto& functionDef = dynamic_cast<FunctionDefinition const&>(*_memberAccess.annotation().referencedDeclaration);

			processFunction(functionDef.resolveVirtual(*m_contract, type.contractDefinition().superContract(*m_contract)), _memberAccess.annotation());

			return true;
		}
	}

	return true;
}

void FunctionCallGraphBuilder::endVisit(FunctionCall const& _functionCall)
{
	auto* functionType = dynamic_cast<FunctionType const*>(_functionCall.expression().annotation().type);

	if (
		functionType &&
		functionType->kind() == FunctionType::Kind::Internal &&
		!functionType->hasDeclaration()
	)
		add(m_currentDispatch, &_functionCall);
}

void FunctionCallGraphBuilder::visitCallable(CallableDeclaration const* _callable)
{
	solAssert(!m_graph->edges.count(_callable), "");

	auto previousNode = m_currentNode;
	m_currentNode = _callable;

	if (nodeSet(previousNode))
		add(previousNode, _callable);

	_callable->accept(*this);

	m_currentNode = previousNode;
}

void FunctionCallGraphBuilder::visitConstructor(
	ContractDefinition const& _contract,
	vector<ContractDefinition const*>::const_iterator _start,
	vector<ContractDefinition const*>::const_iterator _end
)
{
	if (_start != _end)
		visitConstructor(**_start, _start + 1, _end);

	for (auto const* stateVar: _contract.stateVariables())
		stateVar->accept(*this);

	for (auto arg: _contract.baseContracts())
		arg->accept(*this);

	if (_contract.constructor())
	{
		add(m_currentNode, _contract.constructor());
		_contract.constructor()->accept(*this);
	}
}

bool FunctionCallGraphBuilder::add(Node _caller, ASTNode const* _callee)
{
	solAssert(_callee != nullptr, "");
	auto result = m_graph->edges.find(_caller);

	if (result == m_graph->edges.end())
	{
		m_graph->edges.emplace(_caller, std::set<ASTNode const*, ASTNode::CompareByID>{_callee});
		return true;
	}

	return result->second.emplace(_callee).second;
}

void FunctionCallGraphBuilder::processFunction(CallableDeclaration const& _callable, ExpressionAnnotation const& _annotation)
{
	if (m_graph->edges.count(&_callable))
		return;

	// Create edge to creation dispatch
	if (!_annotation.calledDirectly)
		add(m_currentDispatch, &_callable);
	visitCallable(&_callable);
}

}
