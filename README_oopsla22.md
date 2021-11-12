# Trillium

## Compiling

The development is known to compile with

- `coq`: see the `opam` file
- `coq-iris` : see the `opam` file
- `coq-stdpp` : see the `opam` file
- `paco` : see the `opam` file

To install the dependencies, you have to add the following opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `opam update` followed by `make build-dep` to
install the right versions of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores. Be aware that compiling the full development takes quite a bit of
time, approximately 20-30 minutes.

## Directory Structure

- [`vendor/aneris/trace_program_logic`](vendor/aneris/trace_program_logic): The Trillium logic

- [`vendor/aneris/theories`](vendor/aneris/theories): Aneris/The AnerisLang instantiation of Trillium

- `theories/`
  * [`minimal_example/`](theories/minimal_example/): Minimal example
  * [`transaction_commit/`](theories/transaction_commit/): Two-phase commit
  * [`consensus/`](theories/consensus/): Single-decree Paxos
  * [`crdt/`](theories/crdt/): CRDTs

- `vendor/aneris/trace_program_logic/theories/`
  * [`heap_lang`](vendor/aneris/trace_program_logic/theories/heap_lang/): The HeapLang instantiation of Trillium for fair termination.
  * [`heap_lang/examples`](vendor/aneris/trace_program_logic/theories/heap_lang/examples): The Yes/No example
