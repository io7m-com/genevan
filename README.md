genevan
===

[![Maven Central](https://img.shields.io/maven-central/v/com.io7m.genevan/com.io7m.genevan.svg?style=flat-square)](http://search.maven.org/#search%7Cga%7C1%7Cg%3A%22com.io7m.genevan%22)
[![Maven Central (snapshot)](https://img.shields.io/maven-metadata/v?metadataUrl=https%3A%2F%2Fcentral.sonatype.com%2Frepository%2Fmaven-snapshots%2Fcom%2Fio7m%2Fgenevan%2Fcom.io7m.genevan%2Fmaven-metadata.xml&style=flat-square)](https://central.sonatype.com/repository/maven-snapshots/com/io7m/genevan/)
[![Codecov](https://img.shields.io/codecov/c/github/io7m-com/genevan.svg?style=flat-square)](https://codecov.io/gh/io7m-com/genevan)
![Java Version](https://img.shields.io/badge/21-java?label=java&color=e6c35c)

![com.io7m.genevan](./src/site/resources/genevan.jpg?raw=true)

| JVM | Platform | Status |
|-----|----------|--------|
| OpenJDK (Temurin) Current | Linux | [![Build (OpenJDK (Temurin) Current, Linux)](https://img.shields.io/github/actions/workflow/status/io7m-com/genevan/main.linux.temurin.current.yml)](https://www.github.com/io7m-com/genevan/actions?query=workflow%3Amain.linux.temurin.current)|
| OpenJDK (Temurin) LTS | Linux | [![Build (OpenJDK (Temurin) LTS, Linux)](https://img.shields.io/github/actions/workflow/status/io7m-com/genevan/main.linux.temurin.lts.yml)](https://www.github.com/io7m-com/genevan/actions?query=workflow%3Amain.linux.temurin.lts)|
| OpenJDK (Temurin) Current | Windows | [![Build (OpenJDK (Temurin) Current, Windows)](https://img.shields.io/github/actions/workflow/status/io7m-com/genevan/main.windows.temurin.current.yml)](https://www.github.com/io7m-com/genevan/actions?query=workflow%3Amain.windows.temurin.current)|
| OpenJDK (Temurin) LTS | Windows | [![Build (OpenJDK (Temurin) LTS, Windows)](https://img.shields.io/github/actions/workflow/status/io7m-com/genevan/main.windows.temurin.lts.yml)](https://www.github.com/io7m-com/genevan/actions?query=workflow%3Amain.windows.temurin.lts)|

## genevan

The `genevan` package provides a simple generic version negotiation algorithm.

## Features

* Protocol-independent; the package provides version negotiation _semantics_
  without reference to any specific communications protocol.
* Formal specification with proofs of correctness of various properties of
  the protocol.
* Written in pure Java 21.
* High coverage automated test suite.
* [OSGi-ready](https://www.osgi.org/).
* [JPMS-ready](https://en.wikipedia.org/wiki/Java_Platform_Module_System).
* ISC license.

## Informal Description

A server provides a list of protocol names, and each protocol name has a list
of supported version numbers. Call this list `ssp`.

A client provides a list of protocol names, and each protocol name has a list
of supported version numbers. Call this list `csp`.

The server provides `ssp` to the client, and the client removes all of the
elements of `ssp` that do not appear in `csp`. The client then further filters
the list by removing all but the highest version numbers for each named
protocol. Call this filtered list `cfsp`.

If `cfsp` contains a single protocol name and version, the client sends this
protocol name and version to the server, the server confirms the selection,
and the client and server communicate using that version of that protocol
from that point onwards. The negotiation algorithm is completed.

If `cfsp` contains more than a single protocol name and version, the client
consults a possibly-empty list of _preferred_ protocol names.
Call this list `cpp`. The first element of `cpp` that has the same name as
an element in `csfp` is selected, the client sends this protocol name and
version to the server, the server confirms the selection, and the client and
server communicate using that version of that protocol from that point onwards.
The negotiation algorithm is completed.

If no elements of `cpp` match any elements in `cfsp`, then the client and
server are in an _ambiguous_ state: They both have multiple protocols and
versions in common, but there is no deterministic way to pick one;
communcation ends at this point with an error.

At any point, if the client tries to send a protocol name and version that
the server does not support, communication ends at that point with an error.

## Formal Description

A formal description of the protocol, including proofs of correctness, are
provided in the given [Coq development](src/main/coq/genevan.v).

A _protocol version_ consists of a pair of natural numbers representing the
_major_ and _minor_ version of the protocol:

```
Inductive ProtoVersion := {
  prMajor : nat;
  prMinor : nat
}.
```

A _protocol name_ is a string.

```
Definition ProtoName := string.
```

A _protocol identifier_ is the combination of a protocol name and version:

```
Inductive ProtoIdentifier := {
  prName    : ProtoName;
  prVersion : ProtoVersion
}.
```

Protocol versions are totally ordered, with the order defined as the
comparison between major versions, followed by the comparison between minor
versions:

```
Definition protoVersionCmp (p0 p1 : ProtoVersion) : comparison :=
  match Nat.compare (prMajor p0) (prMajor p1) with
  | Eq => Nat.compare (prMinor p0) (prMinor p1)
  | Lt => Lt
  | Gt => Gt
  end.
```

The _maximum_ of two protocol versions `x` and `y` is defined accordingly:

```
Definition max (x y : ProtoVersion) : ProtoVersion :=
  match protoVersionCmp x y with
  | Eq => x
  | Lt => y
  | Gt => x
  end.
```

The `max` function is reflexive, commutative, and associative. Accordingly,
given a non-empty list of protocol versions, the _maximum_ of the list is
defined:

```
Fixpoint maxList
  (xs : list ProtoVersion)
: option ProtoVersion :=
  match xs with
  | []      => None
  | y :: ys =>
    match maxList ys with
    | None   => Some y
    | Some w => Some (max y w)
    end
  end.
```

An empty list has no maximum.

The server exposes a list of _protocol identifiers_. We need to compare the
list of _protocol identifiers_ held by the client with those held by the server.
A _protocol identifier_ is said to be _supported by_ another protocol identifier
if the name and major version match:

```
Definition isSupportedBy
  (x y : ProtoIdentifier)
: Prop :=
  (prName x) = (prName y) /\ (prMajor (prVersion x) = prMajor (prVersion y)).
```

The `isSupportedBy` relation is reflexive, transitive, and symmetric (it
is an equivalence relation). It is also decidable, as equality of names and
version numbers is decidable.

The result of attempting to negotiate a protocol is either success or failure,
with failure cases being limited to ambiguity, or no suitable protocol being
available.

```
Inductive Error :=
  | ErrorNoSolution
  | ErrorAmbiguous : list ProtoIdentifier -> Error.

Inductive Result (A : Set) : Set :=
  | Success : A     -> Result A
  | Failure : Error -> Result A.
```

Given a list of protocols supported on the server side, and a list of protocols
supported on the client side, we first remove all unsupported protocols:

```
Definition bestVersionsOfAll
  (identifiers : list ProtoIdentifier)
: list ProtoIdentifier :=
  withoutOptions (bestVersionsOfAllOpt identifiers).
```

We can then pick a _best_ protocol without any attempt made to avoid ambiguity:

```
Definition solveWithoutDisambiguation
  (serverSupports : list ProtoIdentifier)
  (clientSupports : list ProtoIdentifier)
: Result ProtoIdentifier :=
  match withoutUnsupported serverSupports clientSupports with
  | Failure _ f         => Failure _ f
  | Success _ supported =>
    let bestVersions := bestVersionsOfAll supported in
      match bestVersions with
      | []  => Failure _ ErrorNoSolution
      | [x] => Success _ x
      | xs  => Failure _ (ErrorAmbiguous xs)
      end
  end.
```

If the result is ambiguous, we then _disambiguate_ by picking a protocol from
a provided client-side list:

```
Fixpoint disambiguate
  (xs          : list ProtoIdentifier)
  (preferences : list ProtoName)
: Result ProtoIdentifier :=
  match preferences with
  | []      => Failure _ (ErrorAmbiguous xs)
  | p :: ps =>
    match findWithName xs p with
    | Some r => Success _ r
    | None   => disambiguate xs ps
    end
  end.

Definition solve
  (serverSupports : list ProtoIdentifier)
  (clientSupports : list ProtoIdentifier)
  (preferences    : list ProtoName)
: Result ProtoIdentifier :=
  match solveWithoutDisambiguation serverSupports clientSupports with
  | Success _ r                   => Success _ r
  | Failure _ ErrorNoSolution     => Failure _ ErrorNoSolution
  | Failure _ (ErrorAmbiguous xs) => disambiguate xs preferences
  end.
```

As mentioned, see the `genevan.v` development for the exact definitions of
all functions, and proofs of various properties of the protocol.

## Usage

Create a _protocol solver_:

```
var solver =
  GenProtocolSolver.create();
```

Supply the solver with the protocol names and versions that the server supports,
the protocol names and versions that the client supports, and a possibly-empty
list of protocol names that the client prefers. The solver will pick the
_best_ protocol to send to the server, or it will throw an
`GenProtocolException` explaining why it could not pick:

```
Collection<? extends GenProtocolServerEndpointType> serverSupports;
Collection<? extends GenProtocolClientHandlerType> clientSupports;
List<String> preferProtocols;

var solved =
  solver.solve(
    serverSupports,
    clientSupports,
    preferProtocols
  );
```

