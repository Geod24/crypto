/*******************************************************************************

    Low level utilities to perform Schnorr signatures on Curve25519.

    Through this module, lowercase letters represent scalars and uppercase
    letters represent points. Multiplication of a scalar by a point,
    which is adding a point to itself multiple times, is represented with '*',
    e.g. `a * G`. Uppercase letters are point representations of scalars,
    that is, the scalar multipled by the generator, e.g. `r == r * G`.
    `x` is the private key, `X` is the public key, and `H()` is the Blake2b
    512 bits hash reduced to a scalar in the field.

    Following the Schnorr BIP (see links), signatures are of the form
    `(R,s)` and satisfy `s * G = R + H(X || R || m) * X`.
    `r` is refered to as the nonce and is a cryptographically randomly
    generated number that should neither be reused nor leaked.

    Signature_Aggregation:
    Since Schnorr signatures use a linear equation, they can be simply
    combined with addition, enabling `O(1)` signature verification
    time and `O(1)` and `O(1)` signature size.
    Additionally, since the `c` factor does not depend on EC operation,
    we can do batch verification, enabling us to speed up verification
    when verifying large amount of data (e.g. a block).

    See_Also:
      - https://en.wikipedia.org/wiki/Curve25519
      - https://en.wikipedia.org/wiki/Schnorr_signature
      - https://medium.com/blockstream/reducing-bitcoin-transaction-sizes-with-x-only-pubkeys-f86476af05d7

    TODO:
      - Audit GDC and LDC generated code
      - Proper audit

    Copyright:
        Copyright (c) 2019 BOS Platform Foundation Korea
        All rights reserved.

    License:
        MIT License. See LICENSE for details.

*******************************************************************************/

module agora.crypto.Schnorr;

import agora.crypto.Types;
import agora.crypto.Hash;
import agora.crypto.ECC;

import std.algorithm;
import std.range;


/// Single signature example
nothrow @nogc @safe unittest
{
    Pair kp = Pair.random();
    auto signature = sign(kp, "Hello world");
    assert(verify(kp.V, signature, "Hello world"));
}

/// Multi-signature example
nothrow @nogc @safe unittest
{
    // Setup
    static immutable string secret = "BOSAGORA for the win";
    Pair kp1 = Pair.random();
    Pair kp2 = Pair.random();
    Pair R1 = Pair.random();
    Pair R2 = Pair.random();
    Point R = R1.V + R2.V;
    Point X = kp1.V + kp2.V;

    const sig1 = sign(kp1.v, X, R, R1.v, secret);
    const sig2 = sign(kp2.v, X, R, R2.v, secret);
    const sig3 = Sig(R, Sig.fromBlob(sig1).s + Sig.fromBlob(sig2).s).toBlob();

    // No one can verify any of those individually
    assert(!verify(kp1.V, sig1, secret));
    assert(!verify(kp1.V, sig2, secret));
    assert(!verify(kp2.V, sig2, secret));
    assert(!verify(kp2.V, sig1, secret));
    assert(!verify(kp1.V, sig3, secret));
    assert(!verify(kp2.V, sig3, secret));

    // But multisig works
    assert(verify(X, sig3, secret));
}

/*******************************************************************************

    Extract the R from (R, s) of a binary representation of a signature

    Params:
        sig = the binary representation of the schnorr signature

    Returns:
        the R from the (R, s) pair

*******************************************************************************/

public Point extractNonce (Signature sig) @safe @nogc nothrow pure
{
    return Sig.fromBlob(sig).R;
}

///
@safe @nogc nothrow /*pure*/ unittest
{
    const R = Pair.random();
    const kp = Pair.random();
    const sig = sign(kp.v, kp.V, R.V, R.v, "foo");
    assert(extractNonce(sig) == R.V);
}

/*******************************************************************************
    Represent a signature (R, s)

    Note that signatures get passed around as binary blobs
    (see `agora.common.Types`), so this type is named `Sig` to avoid ambiguity.

*******************************************************************************/

public struct Sig
{
    /// Commitment
    public Point R;
    /// Proof
    public Scalar s;

    static assert(Signature.sizeof == typeof(this).sizeof);

    /// Converts this signature to a BitBlob matching `agora.common.Types`
    public Signature toBlob () const pure nothrow @nogc @safe
    {
        typeof(return) ret;
        ret[0 .. Point.sizeof][] = this.R.data[];
        ret[Point.sizeof .. $][] = this.s.data[];
        return ret;
    }

    /// Deserialize a binary blob into a signature
    public static Sig fromBlob (in Signature s) pure nothrow @nogc @safe
    {
        return Sig(Point(s[0 .. Point.sizeof]), Scalar(s[Point.sizeof .. $]));
    }
}

/// Represent the message to hash (part of `c`)
private struct Message (T)
{
    public Point X;
    public Point R;
    public T     message;
}

/// Single-signer trivial API
public Signature sign (T) (in Pair kp, scope const auto ref T data)
    nothrow @nogc @safe
{
    const R = Pair.random();
    return sign!T(kp.v, kp.V, R.V, R.v, data);
}

/// Single-signer privkey API
public Signature sign (T) (in Scalar privateKey, scope const auto ref T data)
    nothrow @nogc @safe
{
    const R = Pair.random();
    return sign!T(privateKey, privateKey.toPoint(), R.V, R.v, data);
}

/// Sign with a given `r` (warning: `r` should never be reused with `x`)
public Signature sign (T) (in Pair kp, in Pair r, scope const auto ref T data)
{
    return sign!T(kp.v, kp.V, r.V, r.v, data);
}

/// Complex API, allow multisig
public Signature sign (T) (
    in Scalar x, in Point X, in Point R, in Scalar r, scope const auto ref T data)
    nothrow @nogc @trusted
{
    /*
      G := Generator point:
      15112221349535400772501151409588531511454012693041857206046113283949847762202,
      46316835694926478169428394003475163141307993866256225615783033603165251855960
      x := private key
      X := public key (x.G)
      r := random number
      R := commitment (r.G)
      c := Hash(X || R || message)

      Proof = (R, s)
      Signature/Verify: R + c*X == s.G
      Multisig:
      R = (r0 + r1 + rn).G == (R0 + R1 + Rn)
      X = (X0 + X1 + Xn)
      To get `c`, need to precommit `R`
     */
    // Compute the challenge and reduce the hash to a scalar
    Scalar c = hashFull(const(Message!T)(X, R, data));
    // Compute `s` part of the proof
    Scalar s = r + (c * x);
    return Sig(R, s).toBlob();
}

/*******************************************************************************

    Verify that a signature matches the provided data

    Params:
      T = Type of data being signed
      X = The point corresponding to the public key
      sig = Signature to verify
      data = Data to sign (the hash will be signed)

    Returns:
      Whether or not the signature is valid for (X, s, data).

*******************************************************************************/

public bool verify (T) (in Point X, in Signature sig, scope const auto ref T data)
    nothrow @nogc @trusted
{
    Sig s = Sig.fromBlob(sig);
    // First check if Scalar from signature is valid
    if (!s.s.isValid())
        return false;
    /// Compute `s.G`
    auto S = s.s.toPoint();
    // Now check that provided Point X is valid
    if (!X.isValid())
        return false;
    // Also check the Point R from the Signature
    if (!s.R.isValid())
        return false;
    // Compute the challenge and reduce the hash to a scalar
    Scalar c = hashFull(const(Message!T)(X, s.R, data));
    // Compute `R + c*X`
    Point RcX = s.R + (c * X);
    return S == RcX;
}

// Valid signing test with valid scalar
nothrow @nogc @safe unittest
{
    Pair kp = Pair.fromScalar(Scalar(`0x074360d5eab8e888df07d862c4fc845ebd10b6a6c530919d66221219bba50216`));
    static immutable string message = "Bosagora:-)";
    auto signature = sign(kp, message);
    assert(verify(kp.V, signature, message));
}

// Valid with scalar value 1
nothrow @nogc @safe unittest
{
    Pair kp = Pair.fromScalar(Scalar(`0x0000000000000000000000000000000000000000000000000000000000000001`));
    static immutable string message = "Bosagora:-)";
    auto signature = sign(kp, message);
    assert(verify(kp.V, signature, message));
}

// Largest value for Scalar. One less than Ed25519 prime order l where l=2^252 + 27742317777372353535851937790883648493
nothrow @nogc @safe unittest
{
    Pair kp = Pair.fromScalar(Scalar(`0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ec`));
    static immutable string message = "Bosagora:-)";
    auto signature = sign(kp, message);
    assert(verify(kp.V, signature, message));
}

// Not valid with blank signature
nothrow @nogc @safe unittest
{
    Pair kp = Pair.fromScalar(Scalar(`0x074360d5eab8e888df07d862c4fc845ebd10b6a6c530919d66221219bba50216`));
    static immutable string message = "Bosagora:-)";
    Signature signature;
    assert(!verify(kp.V, signature, message));
}

nothrow @nogc @safe unittest
{
    static immutable string secret = "BOSAGORA for the win";
    Pair kp1 = Pair.random();
    Pair kp2 = Pair.random();
    auto sig1 = sign(kp1, secret);
    auto sig2 = sign(kp2, secret);
    assert(verify(kp1.V, sig1, secret));
    assert(!verify(kp1.V, sig2, secret));
    assert(verify(kp2.V, sig2, secret));
    assert(!verify(kp2.V, sig1, secret));
}

// invalid signing test with invalid Public Key Point X
nothrow @nogc @safe unittest
{
    Pair kp = Pair.fromScalar(Scalar(`0x074360d5eab8e888df07d862c4fc845ebd10b6a6c530919d66221219bba50216`));
    static immutable string message = "Bosagora:-)";
    auto signature = sign(kp, message);
    auto invalid = Point("0xab4f6f6e85b8d0d38f5d5798a4bdc4dd444c8909c8a5389d3bb209a18610511c");
    assert(!verify(invalid, signature, message));
}

// invalid signing test with invalid Point R in Signature
nothrow @nogc @safe unittest
{
    Pair kp = Pair.fromScalar(Scalar(`0x074360d5eab8e888df07d862c4fc845ebd10b6a6c530919d66221219bba50216`));
    static immutable string message = "Bosagora:-)";
    auto signature = sign(kp, message);
    Signature invalid_sig = Sig(Point("0xab4f6f6e85b8d0d38f5d5798a4bdc4dd444c8909c8a5389d3bb209a18610511c"),
        Sig.fromBlob(signature).s).toBlob();
    assert(!verify(kp.V, invalid_sig, message));
}

// example of extracting the private key from an insecure signature scheme
// which did not include 'r' during the signing
// https://tlu.tarilabs.com/cryptography/digital_signatures/introduction_schnorr_signatures.html#why-do-we-need-the-nonce
/*@nogc*/ @safe unittest
{
    static immutable string message = "BOSAGORA for the win";

    Pair kp = Pair.random();  // key-pair
    Scalar c = hashFull(message);  // challenge
    Scalar s = (kp.v * c);  // signature

    // known public data of the node
    Point K = kp.V;

    // other nodes verify
    assert(s.toPoint() == K * c);

    // but the other node can also extract the private key!
    Scalar stolen_key = s * c.invert();
    assert(stolen_key == kp.v);
}

// possibly secure signature scheme (requires proving ownership of private key)
/*@nogc*/ @safe unittest
{
    static immutable string message = "BOSAGORA for the win";

    Pair kp = Pair.random();  // key-pair
    Pair Rp = Pair.random();  // (R, r), the public and private nonce
    Scalar c = hashFull(message);  // challenge
    Scalar s = Rp.v + (kp.v * c);  // signature

    // known public data of the node
    Point K = kp.V;
    Point R = Rp.V;

    // other nodes verify
    assert(s.toPoint() == R + (K * c));

    // other nodes cannot extract the private key, they don't know 'r'
    Scalar stolen_key = s * c.invert();
    assert(stolen_key != kp.v);
}

/// Single-signer as part of multi-sig
public Scalar multiSigSign (in Scalar r, in Scalar v, in Scalar c)
    nothrow @nogc @safe
{
    return r + (v * c);
}

/// multi-sig verify
public bool multiSigVerify (in Sig sig, in Point sumV, in Scalar c)
    nothrow @nogc @safe
{
    return sig.s.toPoint() == sig.R + (sumV * c);
}

/// multi-sig combine
public Sig multiSigCombine (S)(const S sigs) nothrow @nogc @safe
{
    Point sum_R = sigs.map!(x => x.R).sum(Point.init);
    Scalar sum_s = sigs.map!(x => x.s).sum(Scalar.init);
    return Sig(sum_R, sum_s);
}

/// testing multiSig for block signing
/*@nogc*/ @safe unittest
{
    static immutable string message = "BOSAGORA for the win";

    const Scalar c = hashFull(message);  // challenge

    const kp1_K = Pair.random();  // key-pair
    const kp1_R = Pair.random();  // (R, r), the public and private nonce

    // first signer
    const Scalar s1 = multiSigSign(kp1_R.v, kp1_K.v, c);

    const kp2_K = Pair.random();  // key-pair
    const kp2_R = Pair.random();  // (R, r), the public and private nonce

    // second signer
    const Scalar s2 = multiSigSign(kp2_R.v, kp2_K.v, c);

    // verification of individual signatures
    assert(s1.toPoint() == kp1_R.V + (kp1_K.V * c));
    assert(s2.toPoint() == kp2_R.V + (kp2_K.V * c));

    Sig[] sigs = [ Sig(kp1_R.V, s1), Sig(kp2_R.V, s2) ];
    // "multi-sig" - collection of one or more signatures
    Sig two_sigs = multiSigCombine(sigs);

    const sumK = kp1_K.V + kp2_K.V;
    // verification of combined signatures
    assert(multiSigVerify(two_sigs, sumK, c));

    // Now add one more signature
    const kp3_K = Pair.random();  // key-pair
    const kp3_R = Pair.random();  // (R, r), the public and private nonce

    // third signer
    const Scalar s3 = multiSigSign(kp3_R.v, kp3_K.v, c);
    // Add third signature
    Sig three_sigs = multiSigCombine([ two_sigs, Sig(kp3_R.V, s3) ]);
    // verification of updated combined signatures
    const three_sumK = sumK + kp3_K.V;
    assert(multiSigVerify(three_sigs, three_sumK, c));
}

// rogue-key attack
// see: https://tlu.tarilabs.com/cryptography/digital_signatures/introduction_schnorr_signatures.html#key-cancellation-attack
// see: https://blockstream.com/2018/01/23/en-musig-key-aggregation-schnorr-signatures/#:~:text=not%20secure.
@safe unittest
{
    static immutable string message = "BOSAGORA for the win";

    // alice
    const Pair kp1 = Pair.random(); // key-pair
    const Pair R1 = Pair.random();  // (R, r), the public and private nonce

    // bob
    const Pair kp2 = Pair.random(); // ditto
    const Pair R2 = Pair.random();  // ditto

    auto R = R1.V + R2.V;
    auto X = kp1.V + kp2.V;
    Scalar c = hashMulti(X, R, message);  // challenge

    Scalar s1 = R1.v + (kp1.v * c);
    Scalar s2 = R2.v + (kp2.v * c);
    Scalar multi_sig = s1 + s2;
    assert(multi_sig.toPoint() == R + (X * c));

    // now assume that bob lied about his V and R during the co-operative phase.
    auto bobV = kp2.V - kp1.V;
    auto bobR = R2.V - R1.V;
    X = kp1.V + bobV;
    R = R1.V + bobR;
    c = Scalar(hashMulti(X, R, message));

    // bob signed the message alone, without co-operation from alice. it passes!
    Scalar bob_sig = R2.v + (kp2.v * c);
    assert(bob_sig.toPoint() == R + (X * c));
}

// ditto, but using multi-sig
/*@nogc*/ @safe unittest
{
    static immutable string message = "BOSAGORA for the win";

    Scalar c = hashFull(message);  // challenge

    Pair kp_1 = Pair.random();  // key-pair
    Pair Rp_1 = Pair.random();  // (R, r), the public and private nonce
    Scalar s_1 = Rp_1.v + (kp_1.v * c);  // signature

    Pair kp_2 = Pair.random();  // key-pair
    Pair Rp_2 = Pair.random();  // (R, r), the public and private nonce
    Scalar s_2 = Rp_2.v + (kp_2.v * c);  // signature

    // known public data of the nodes
    Point K_1 = kp_1.V;
    Point R_1 = Rp_1.V;

    Point K_2 = kp_2.V;
    Point R_2 = Rp_2.V;

    // verification of individual signatures
    assert(s_1.toPoint() == R_1 + (K_1 * c));
    assert(s_2.toPoint() == R_2 + (K_2 * c));

    // "multi-sig" - collection of one or more signatures
    auto sum_s = s_1 + s_2;
    assert(sum_s.toPoint() ==
        (R_1 + (K_1 * c)) +
        (R_2 + (K_2 * c)));

    // Or the equivalent:
    assert(sum_s.toPoint() ==
        (R_1 + R_2) + (K_1 * c) + (K_2 * c));
}
