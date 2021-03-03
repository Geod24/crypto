/*******************************************************************************

    Function definition and helper related to hashing

    The actual definition of the `Hash` type is in `agora.common.Types`,
    as parts of the system might pass along `Hash` without having to know
    what / how they were produced.

    However, this module expose functionalities for modules that want to do
    hashing. The interface is designed so that this module knows about the
    hash types, and aggregates implementing the interface only deal with their
    members.

    Due to a language limitation (one can't overload based on return value),
    this module expose two main functions:
    - `hashFull(T)`, which returns a `Hash`
    - `hashPart(T, HashDg)` which does not return anything and should be used
      to accumulate data to hash.

    For safety reason, a data structure currently need to explicitly define
    a `hash` function to support hashing.
    This limitation might be lifted in the future, but a few things
    need to be taken into account:
    - Alignment / packing: We can't have unaligned / unpacked structures
      as it would create malleability issues
    - Non-public members: We can't deal with anything non-public (we can use
      `.tupleof` but it's impossible to tell the usage of the member,
      e.g. it could be a cache of the hash)
    - Indirections / references types

    Copyright:
        Copyright (c) 2019 BOS Platform Foundation Korea
        All rights reserved.

    License:
        MIT License. See LICENSE for details.

*******************************************************************************/

module agora.crypto.Hash;

public import agora.crypto.Types;

import libsodium;

import std.bitmanip : nativeToLittleEndian;
import std.traits;

///
nothrow @nogc @safe unittest
{
    static struct SimpleStruct
    {
        ulong foo;
        string bar;
    }

    static struct ComplexStruct
    {
        string irrelevant;
        string bar;
        ulong foo;

        void computeHash (scope HashDg dg) const nothrow @safe @nogc
        {
            // We can hash in any order we want, and ignore anything we want
            hashPart(this.foo, dg);
            hashPart(this.bar, dg);
        }
    }

    const st = SimpleStruct(42, "42");
    // This gives the same result as if `foo` and the content of `bar` were
    // stored contiguously in memory and hashed
    Hash r2 = hashFull(st);
    // Result is stable
    assert(hashFull(SimpleStruct(42, "42")) == r2);
    assert(hashFull(ComplexStruct("Hello World", "42", 42)) == r2);

    // Alternatively, simple string messages can be hashed
    Hash abc = hashFull("abc");

    // And any basic type
    Hash ulm = hashFull(ulong.max);
}

/// Type of delegate passed to `hash` function when there's a state
public alias HashDg = void delegate(in ubyte[]) /*pure*/ nothrow @safe @nogc;


/*******************************************************************************

    Hash a given data structure using BLAKE2b into `state`

    Note that there is no overload for signed types, as only the binary
    representation matters for hashing.

    Params:
      T = Type of struct to hash
      record = Instance of `T` to hash
      state  = State delegate, when this struct is nested in another.

    Returns:
      The `Hash` representing this instance

*******************************************************************************/

public Hash hashFull (T) (scope const auto ref T record)
    nothrow @nogc @trusted
{
    Hash hash = void;
    crypto_generichash_state state;
    crypto_generichash_init(&state, null, 0, Hash.sizeof);
    scope HashDg dg = (in ubyte[] data) @trusted {
        crypto_generichash_update(&state, data.ptr, data.length);
    };
    hashPart(record, dg);
    crypto_generichash_final(&state, hash[].ptr, Hash.sizeof);
    return hash;
}

/// Ditto
public void hashPart (T) (scope const auto ref T record, scope HashDg hasher)
    /*pure*/ nothrow @nogc
{
    // Workaround for https://issues.dlang.org/show_bug.cgi?id=21659
    // It will be fixed in v2.096.0.
    // The `__c_ulonglong` type is not available on Windows,
    // so instead use an alias and a dummy type;
    version (Posix)
        import core.stdc.config : __c_ulonglong;
    else
        enum __c_ulonglong { Unused }

    static if (is(typeof(T.init.computeHash(HashDg.init))))
        record.computeHash(hasher);

    else static if (__traits(compiles, () { const ubyte[] r = T.init[]; }))
    {
        hashVarInt(record[].length, hasher);
        hasher(record[]);
    }
    else static if (isNarrowString!T)
    {
        hashVarInt(record.length, hasher);
        hasher(cast(const(ubyte[]))record);
    }
    else static if (is(immutable(T) == immutable(ubyte[])))
    {
        hashVarInt(record.length, hasher);
        hasher(record);
    }
    else static if (is(T : E[], E))
    {
        hashVarInt(record.length, hasher);
        foreach (ref r; record)
            hashPart(r, hasher);
    }
    else static if (is(immutable(ubyte) == immutable(T)))
        hasher((cast(ubyte*)&record)[0 .. ubyte.sizeof]);
    else static if (is(immutable(T) == immutable(__c_ulonglong)))
    {
        static assert(__c_ulonglong.sizeof == ulong.sizeof);
        hasher(nativeToLittleEndian!ulong(record)[0 .. ulong.sizeof]);
    }
    else static if (isScalarType!T)
        hasher(nativeToLittleEndian(record)[0 .. T.sizeof]);

    else
        foreach (const ref field; record.tupleof)
            hashPart(field, hasher);
}

/*******************************************************************************

    Hash the variable-length binary format of an unsigned integer

    VarInt Size
    size <= 0xFC(252)  -- 1 byte   ubyte
    size <= USHORT_MAX -- 3 bytes  (0xFD + ushort)
    size <= UINT_MAX   -- 5 bytes  (0xFE + uint)
    size <= ULONG_MAX  -- 9 bytes  (0xFF + ulong)

    Params:
        T = Type of unsigned integer to hash
        var = Instance of `T` to hash
        dg  = Hash delegate

    Returns:
        The hashed variable length integer

*******************************************************************************/

private void hashVarInt (T) (const T var, scope HashDg hasher)
    @trusted @nogc
    if (isUnsigned!T)
{
    assert(var >= 0);
    static immutable ubyte[] type = [0xFD, 0xFE, 0xFF];
    if (var <= 0xFC)
        hasher((cast(ubyte*)&(*cast(ubyte*)&var))[0 .. 1]);
    else if (var <= ushort.max)
    {
        hasher(type[0..1]);
        hasher((cast(ubyte*)&(*cast(ushort*)&var))[0 .. ushort.sizeof]);
    }
    else if (var <= uint.max)
    {
        hasher(type[1..2]);
        hasher((cast(ubyte*)&(*cast(uint*)&var))[0 .. uint.sizeof]);
    }
    else if (var <= ulong.max)
    {
        hasher(type[2..3]);
        hasher((cast(ubyte*)&(*cast(ulong*)&var))[0 .. ulong.sizeof]);
    }
    else
        assert(0, "Hash failure. Array length too large.");
}

// Endianness test
unittest
{
    assert(hashFull(0x0102).toString()             == "0xcab9b7ff335bf7ce6e801192cf57ec97a97d91d84de93201399ffa17cd2cd07" ~
                                                      "1fcd7cd62d92b5fa5cc4de8bb4dd7a556cf524a9c597cdb5a8917aaf119eded8c");
    assert(hashFull(0x01020304).toString()         == "0xe01ad62eb0275971a2973ba15f44b0b90e2da88d871ba4fda1430353b4cfe290" ~
                                                      "3555d974665b42e34805c9730249a0905f5b433e1cb97f91e1292bb7264b4ecb");
    assert(hashFull(0x0102030405060708).toString() == "0xcda1a14d4efa540dd742bd7a0018823063ece39955b59d6b2ac507ac32f7e06" ~
                                                      "410c64a6334e044508855e86e3c51ca53903371937edfeb8a74fa6a848baae93f");
}
// Test that the implementation actually matches what the RFC gives
nothrow @nogc @safe unittest
{
    // https://tools.ietf.org/html/rfc7693#appendix-A
    static immutable ubyte[] hdata = [
        0xBA, 0x80, 0xA5, 0x3F, 0x98, 0x1C, 0x4D, 0x0D, 0x6A, 0x27, 0x97, 0xB6,
        0x9F, 0x12, 0xF6, 0xE9,
        0x4C, 0x21, 0x2F, 0x14, 0x68, 0x5A, 0xC4, 0xB7, 0x4B, 0x12, 0xBB, 0x6F,
        0xDB, 0xFF, 0xA2, 0xD1,
        0x7D, 0x87, 0xC5, 0x39, 0x2A, 0xAB, 0x79, 0x2D, 0xC2, 0x52, 0xD5, 0xDE,
        0x45, 0x33, 0xCC, 0x95,
        0x18, 0xD3, 0x8A, 0xA8, 0xDB, 0xF1, 0x92, 0x5A, 0xB9, 0x23, 0x86, 0xED,
        0xD4, 0x00, 0x99, 0x23
    ];
    const abc_exp = Hash(hdata, /*isLittleEndian:*/ true);

    // If we use a string of "abc" the length is also hashed so we use ComposedString
    static struct ComposedString
    {
        char a;
        char b;
        char c;
    }
    Hash abc = hashFull(ComposedString('a', 'b', 'c'));
    assert(abc == abc_exp);

    static struct ComposedWithComputeHash
    {
        public char c0;
        private int irrelevant;
        public char c1;
        private ulong say_what;
        public char c2;
        private string baguette;

        public void computeHash (scope HashDg dg) const nothrow @safe @nogc
        {
            // We can hash in any order we want so lets reverse the order and skip some fields
            hashPart(this.c2, dg);
            hashPart(this.c1, dg);
            hashPart(this.c0, dg);
        }
    }
    Hash cba = hashFull(ComposedWithComputeHash('c', 5, 'b', 42, 'a', "flute"));
    assert(cba == abc_exp);
}

/*******************************************************************************

    Hashes multiple arguments together

    Params:
        T = variadic argument types
        args = the arguments

    Returns:
        the hash of all the arguments

*******************************************************************************/

public Hash hashMulti (T...)(auto ref T args) nothrow @nogc @safe
{
    Hash hash = void;
    crypto_generichash_state state;

    void trustedInit () @trusted
    {
        crypto_generichash_init(&state, null, 0, Hash.sizeof);
    }
    trustedInit();

    scope HashDg dg = (in ubyte[] data) @trusted {
        crypto_generichash_update(&state, data.ptr, data.length);
    };

    static foreach (idx, _; args)
        hashPart(args[idx], dg);
    void trusted () @trusted
    {
        crypto_generichash_final(&state, hash[].ptr, Hash.sizeof);
    }
    trusted();
    assert(hash == hashMulti2(args));
    return hash;
}

public Hash hashMulti2 (T...)(auto ref T args) nothrow @nogc @safe
{
    Hash hash = void;
    crypto_generichash_state state;

    auto dg = () @trusted {
         crypto_generichash_init(&state, null, 0, Hash.sizeof);
        scope HashDg dg = (in ubyte[] data) @trusted {
            crypto_generichash_update(&state, data.ptr, data.length);
        };
        return dg;
    }();

    static foreach (idx, _; args)
        hashPart(args[idx], dg);
    void trusted () @trusted
    {
        crypto_generichash_final(&state, hash[].ptr, Hash.sizeof);
    }
    trusted();
    return hash;
}

///
nothrow @nogc @safe unittest
{
    struct T
    {
        string foo;
        string bar;
    }
    assert(hashFull(T("foo", "bar")) == hashMulti("foo", "bar"));

    static struct S
    {
        public char c0;
        private int unused_1;
        public char c1;
        private int unused_2;
        public char c2;
        private int unused_3;

        public void computeHash (scope HashDg dg) const nothrow @safe @nogc
        {
            hashPart(this.c0, dg);
            hashPart(this.c1, dg);
            hashPart(this.c2, dg);
        }
    }

    auto hash_1 = hashMulti(420, "bpfk", S('a', 0, 'b', 0, 'c', 0));
    auto hash_2 = hashMulti(420, "bpfk", S('a', 1, 'b', 2, 'c', 3));
    assert(hash_1 == hash_2);

    static struct X
    {
        T t;
        S s;
    }
    auto s = S('a', 0, 'b', 0, 'c', 0);
    auto hash_x1 = hashMulti(T("foo", "bar"), 'a', 'b', 'c');
    auto hash_x2 = hashFull(X(T("foo", "bar"), s));
    assert(hash_x1 == hash_x2, "Hash of nested struct with computeHash failed");
}

/// Test that array with struct inside will use computeHash
unittest
{
    static struct S
    {
        public char c0;
        private int unused_1;
        public char c1;

        public void computeHash (scope HashDg dg) const nothrow @safe @nogc
        {
            hashPart(this.c0, dg);
            hashPart(this.c1, dg);
        }
    }
    static struct X
    {
        string foo;
        S[] x;
    }
    static struct X_S
    {
        string foo;
        ubyte len;  // We need to simulate the array size being included
        char c0;
        char c1;
    }
    auto s1 = S('a', 42, 'b');
    auto s = [ s1 ];
    auto hash_x1 = hashFull(X_S("foo", 1, 'a', 'b'));
    auto hash_x2 = hashFull(X("foo", s));
    assert(hash_x1 == hash_x2, "Hash of struct in an array with computeHash failed");
}

// https://github.com/bpfkorea/agora/issues/1331
unittest
{
    import std.format;

    static struct S
    {
        ubyte[] arr1;
        ubyte[] arr2;
    }
    auto s1 = S([0, 1, 2], null);
    auto s2 = S(null, [0, 1, 2]);
    assert(s1.hashFull() != s2.hashFull(),
        format!"%s == %s"(s1, s2));
}
