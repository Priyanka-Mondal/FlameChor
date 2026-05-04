# FlameChor

A Haskell library that extends [HasChor](https://github.com/gshen42/HasChor) with information flow control, consensus, and fault-tolerant language constructs for building secure distributed applications.

FlameChor integrates the [FLAME](https://github.com/owenarden/flame) information flow type system into choreographic programming, allowing developers to write distributed programs that are **secure-by-construction** — the compiler enforces confidentiality, integrity, and availability policies rather than leaving them to runtime checks.

This library is the implementation artifact accompanying the papers:
- *Applying Consensus and Replication Securely with FLAQR* — **IEEE CSF 2022** (Distinguished Paper Award)
- *Flow-Limited Authorization for Consensus, Replication, and Secret Sharing* — **Journal of Computer Security, 2023**

---

## What is Choreographic Programming?

Choreographic programming is a paradigm where a distributed system is described as a single, unified program (a *choreography*) rather than as separate per-process programs. The runtime projects the choreography onto individual participants, eliminating an entire class of communication mismatches by construction.

HasChor provides the choreographic programming foundation. FlameChor layers security on top.

---

## Features

- **Information flow control** — Enforce confidentiality and integrity policies across distributed participants using the FLAME type system
- **Fault-tolerant constructs** — Built-in support for consensus and quorum replication protocols
- **Byzantine fault tolerance** — Programs remain correct even when some participants act maliciously
- **Availability guarantees** — Type-level liveness guarantees for majority quorum protocols under bounded faults
- **Secure-by-construction** — Security properties are verified at compile time, not runtime

---

## Repository Structure

```
FlameChor/
├── HasChor/          # Core HasChor choreography library
├── flame-plugin/     # GHC plugin for FLAME information flow analysis
├── flame-runtime/    # FlameChor runtime
│   ├── src/
│   │   ├── Flame/    # Core FLAME constructs and primitives
│   │   └── MyHasChor/# FlameChor-specific choreography extensions
│   └── playground/   # Example programs
│       ├── bookseller-1-simple/   # Basic choreography example
│       ├── bookseller-2/          # Extended bookseller
│       ├── bookseller-3/          # Bookseller with fault tolerance
│       ├── majorityQuorum/        # Majority quorum consensus
│       ├── pBFT/                  # Practical Byzantine Fault Tolerance
│       └── availFlame/            # Availability with FLAME policies
└── FlameChor.cabal
```

---

## Building

FlameChor uses the Haskell Stack build tool.

**Prerequisites**: GHC, Stack

```bash
git clone https://github.com/Priyanka-Mondal/FlameChor.git
cd FlameChor/flame-runtime
stack build
```

---

## Examples

Examples are in `flame-runtime/playground/`. To run one:

```bash
cd flame-runtime
stack runghc playground/majorityQuorum/Main.hs
```

### Bookseller
A canonical choreographic programming example, extended with FLAME security policies. A buyer and seller negotiate a book purchase with confidentiality guarantees on pricing information.

### Majority Quorum
A distributed consensus protocol where a majority of replicas must agree before a value is committed. Demonstrates FLAQR's availability guarantees under crash faults.

### pBFT
Practical Byzantine Fault Tolerance — a consensus protocol that remains correct even when up to ⌊(n−1)/3⌋ participants are malicious. Demonstrates FLAQR's integrity guarantees under Byzantine faults.

---

## Related Work

This library implements the FLAQR calculus described in:

- Mondal, Algehed, Arden. [*Applying Consensus and Replication Securely with FLAQR*](https://priyanka-mondal.github.io/FLAQR_official.pdf). IEEE CSF 2022. **Distinguished Paper Award.**
- Mondal, Algehed, Arden. [*Flow-Limited Authorization for Consensus, Replication, and Secret Sharing*](https://priyanka-mondal.github.io/FLAQRJCS.pdf). Journal of Computer Security, 2023.
