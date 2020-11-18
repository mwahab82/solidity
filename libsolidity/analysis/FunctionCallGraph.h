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

#pragma once

#include <libsolidity/ast/AST.h>
#include <libsolidity/ast/ASTVisitor.h>

#include <vector>
#include <variant>

namespace solidity::frontend
{

/* Creates a Function call graph for a contract.
 * Includes the following special nodes:
 *  - CreationRoot: All calls made at contract creation originate from this node
 *  - CreationDispatch: Represents the creation dispatch function
 *  - RuntimeDispatch: Represents the dispatch for the runtime part
 *
 *  Nodes are a variant of either the enum SpecialNode or an ASTNode pointer.
 *  ASTNodes are usually inherited from CallableDeclarations
 *  (FunctionDefinition, ModifierDefinition, EventDefinition) but for functions
 *  without declaration it is directly the FunctionCall AST node.
 *
 *  Functions that are not called right away as well as functions without
 *  declarations have an edge to the dispatch node. */
class FunctionCallGraphBuilder: private ASTConstVisitor
{
public:
	enum class SpecialNode { Unset, CreationRoot, CreationDispatch, RuntimeDispatch };

	typedef std::variant<ASTNode const*, SpecialNode> Node;

	struct CompareByID
	{
		using is_transparent = void;

		bool operator()(Node const& _lhs, Node const& _rhs) const
		{
			if (_lhs.index() != _rhs.index())
				return _lhs.index() < _rhs.index();

			if (std::holds_alternative<SpecialNode>(_lhs))
				return std::get<SpecialNode>(_lhs) < std::get<SpecialNode>(_rhs);
			return std::get<ASTNode const*>(_lhs)->id() < std::get<ASTNode const*>(_rhs)->id();
		}
		bool operator()(Node const& _lhs, int64_t _rhs) const
		{
			solAssert(!std::holds_alternative<SpecialNode>(_lhs), "");

			return std::get<ASTNode const*>(_lhs)->id() < _rhs;
		}
		bool operator()(int64_t _lhs, Node const& _rhs) const
		{
			solAssert(!std::holds_alternative<SpecialNode>(_rhs), "");

			return _lhs < std::get<ASTNode const*>(_rhs)->id();
		}
	};

	struct ContractCallGraph
	{
		ContractCallGraph(ContractDefinition const& _contract) :contract(_contract) {}

		/// Contract for which this is the graph
		ContractDefinition const& contract;

		std::map<Node, std::set<ASTNode const*, ASTNode::CompareByID>, CompareByID> edges;

		/// Set of contracts created
		std::set<ContractDefinition const*, ASTNode::CompareByID> createdContracts;
	};

	std::shared_ptr<ContractCallGraph> const create(ContractDefinition const& _contract);

private:
	bool visit(Identifier const& _identifier) override;
	bool visit(NewExpression const& _newExpression) override;
	bool visit(MemberAccess const& _memberAccess) override;
	void endVisit(FunctionCall const& _functionCall) override;

	void visitCallable(CallableDeclaration const* _callable);
	void visitConstructor(
		ContractDefinition const& _contract,
		std::vector<ContractDefinition const*>::const_iterator _start,
		std::vector<ContractDefinition const*>::const_iterator _end
	);

	bool add(Node _caller, ASTNode const* _callee);
	void processFunction(CallableDeclaration const& _callable, ExpressionAnnotation const& _annotation);

	ContractDefinition const* m_contract = nullptr;
	Node m_currentNode = SpecialNode::Unset;
	std::shared_ptr<ContractCallGraph> m_graph = nullptr;
	Node m_currentDispatch = SpecialNode::Unset;
};

}
