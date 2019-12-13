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
/**
 * Unit tests for FixedHash.
 */

#include <libsolutil/FixedHash.h>

#include <boost/test/unit_test.hpp>

#include <cstdint>
#include <sstream>

using namespace std;

namespace solidity::util::test
{

static_assert(std::is_same<h160, FixedHash<20>>());
static_assert(std::is_same<h256, FixedHash<32>>());

BOOST_AUTO_TEST_SUITE(FixedHashTest)

BOOST_AUTO_TEST_CASE(default_constructor)
{
	// NOTE: why support 0-length hash?
	BOOST_CHECK_EQUAL(
		FixedHash<0>{}.hex(),
		""
	);
	BOOST_CHECK_EQUAL(
		FixedHash<0>{}.size,
		0
	);
	BOOST_CHECK_EQUAL(
		FixedHash<1>{}.hex(),
		"00"
	);
	BOOST_CHECK_EQUAL(
		FixedHash<1>{}.size,
		1
	);
	BOOST_CHECK_EQUAL(
		FixedHash<8>{}.hex(),
		"0000000000000000"
	);
	BOOST_CHECK_EQUAL(
		FixedHash<8>{}.size,
		8
	);
	BOOST_CHECK_EQUAL(
		FixedHash<20>{}.hex(),
		"0000000000000000000000000000000000000000"
	);
	BOOST_CHECK_EQUAL(
		FixedHash<20>{}.size,
		20
	);
	BOOST_CHECK_EQUAL(
		FixedHash<32>{}.hex(),
		"0000000000000000000000000000000000000000000000000000000000000000"
	);
	BOOST_CHECK_EQUAL(
		FixedHash<32>{}.size,
		32
	);
}

BOOST_AUTO_TEST_CASE(string_constructor_fromhex)
{
	FixedHash<0> a("");
	BOOST_CHECK_EQUAL(a.size, 0);
	BOOST_CHECK_EQUAL(a.hex(), "");

	FixedHash<8> b("");
	BOOST_CHECK_EQUAL(b.size, 8);
	BOOST_CHECK_EQUAL(b.hex(), "0000000000000000");

	FixedHash<8> c("1122334455667788");
	BOOST_CHECK_EQUAL(c.size, 8);
	BOOST_CHECK_EQUAL(c.hex(), "1122334455667788");

	// NOTE: this should fail?
	FixedHash<8> d("112233445566");
	BOOST_CHECK_EQUAL(d.size, 8);
	BOOST_CHECK_EQUAL(d.hex(), "0000000000000000");

	// NOTE: this should fail...
	FixedHash<8> e("112233445566778899");
	BOOST_CHECK_EQUAL(e.size, 8);
	BOOST_CHECK_EQUAL(e.hex(), "0000000000000000");

	// NOTE: this should fail...
	FixedHash<8> f("0x1122334455667788");
	BOOST_CHECK_EQUAL(f.size, 8);
	BOOST_CHECK_EQUAL(f.hex(), "1122334455667788");
}

BOOST_AUTO_TEST_CASE(string_constructor_frombytes)
{

	FixedHash<0> a("", FixedHash<0>::FromBinary);
	BOOST_CHECK_EQUAL(a.size, 0);
	BOOST_CHECK_EQUAL(a.hex(), "");

	FixedHash<8> b("", FixedHash<8>::FromBinary);
	BOOST_CHECK_EQUAL(b.size, 8);
	BOOST_CHECK_EQUAL(b.hex(), "0000000000000000");

	FixedHash<8> c("abcdefgh", FixedHash<8>::FromBinary);
	BOOST_CHECK_EQUAL(c.size, 8);
	BOOST_CHECK_EQUAL(c.hex(), "6162636465666768");

	// NOTE: this should fail?
	FixedHash<8> d("abcdefg", FixedHash<8>::FromBinary);
	BOOST_CHECK_EQUAL(d.size, 8);
	BOOST_CHECK_EQUAL(d.hex(), "0000000000000000");

	// NOTE: this should fail...
	FixedHash<8> e("abcdefghi", FixedHash<8>::FromBinary);
	BOOST_CHECK_EQUAL(e.size, 8);
	BOOST_CHECK_EQUAL(e.hex(), "0000000000000000");
}

// TOOD: add FixedHash(bytes const&) constructor
// TOOD: add FixedHash(bytesConstRef) constructor
// TODO: add FixedHash(FixedHash<M> const&) constructor

BOOST_AUTO_TEST_CASE(arith_constructor)
{
	FixedHash<20> a(u160(0x1234));
	BOOST_CHECK_EQUAL(
		a.hex(),
		"0000000000000000000000000000000000001234"
	);

	FixedHash<32> b(u256(0x12340000));
	BOOST_CHECK_EQUAL(
		b.hex(),
		"0000000000000000000000000000000000000000000000000000000012340000"
	);
}

BOOST_AUTO_TEST_CASE(to_arith)
{
	FixedHash<20> a{};
	BOOST_CHECK_EQUAL(u160(a), 0);

	FixedHash<32> b("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
	BOOST_CHECK_EQUAL(u256(b), u256("0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"));
}

BOOST_AUTO_TEST_CASE(comparison)
{
	FixedHash<32> a("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
	FixedHash<32> b("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
	FixedHash<32> c("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a471");
	FixedHash<32> d("233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470c5d2460186f7");

	BOOST_CHECK(a == a);
	BOOST_CHECK(b == b);
	BOOST_CHECK(a == b);
	BOOST_CHECK(a != c);
	BOOST_CHECK(a != d);

	// Only equal size comparison is supported.
	BOOST_CHECK(FixedHash<0>{} == FixedHash<0>{});
	BOOST_CHECK(FixedHash<32>{} != b);

	// Only equal size less than comparison is supported.
	BOOST_CHECK(!(a < b));
	BOOST_CHECK(d < c);
	BOOST_CHECK(FixedHash<32>{} < a);
}

BOOST_AUTO_TEST_CASE(indexing)
{
	// NOTE: uses std::array, so "Accessing a nonexistent element through this operator is undefined behavior."

	FixedHash<32> a("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
	BOOST_CHECK_EQUAL(a[0], 0xc5);
	BOOST_CHECK_EQUAL(a[1], 0xd2);
	BOOST_CHECK_EQUAL(a[31], 0x70);
	a[0] = 0xff;
	a[31] = 0x54;
	BOOST_CHECK_EQUAL(a[0], 0xff);
	BOOST_CHECK_EQUAL(a[1], 0xd2);
	BOOST_CHECK_EQUAL(a[31], 0x54);
}

BOOST_AUTO_TEST_CASE(misc)
{
	FixedHash<32> a("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");

	uint8_t* mut_a = a.data();
	uint8_t const* const_a = a.data();
	BOOST_CHECK_EQUAL(mut_a, const_a);
	BOOST_CHECK_EQUAL(memcmp(mut_a, const_a, a.size), 0);

	bytes bytes_a = a.asBytes();
	bytesRef bytesref_a = a.ref();
	bytesConstRef bytesconstref_a = a.ref();

	// There's no printing for bytesRef/bytesConstRef
	BOOST_CHECK(bytes(a.data(), a.data() + a.size) == bytes_a);
	BOOST_CHECK(bytesRef(a.data(), a.size) == bytesref_a);
	BOOST_CHECK(bytesConstRef(a.data(), a.size) == bytesconstref_a);
}

BOOST_AUTO_TEST_CASE(tostream)
{
	std::ostringstream out;
	out << FixedHash<0>{};
	out << FixedHash<4>("44114411");
	out << FixedHash<32>{};
	out << FixedHash<2>("f77f");
	out << FixedHash<1>("1");
	BOOST_CHECK_EQUAL(out.str(), "441144110000000000000000000000000000000000000000000000000000000000000000f77f01");
}

BOOST_AUTO_TEST_SUITE_END()

}
