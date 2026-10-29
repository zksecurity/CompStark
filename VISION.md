# Vision

CompStark is meant to be a Lean library of proof systems with state-of-the-art performance, prover and verifier alike, and state-of-the-art security analysis, proved in Lean, for every configuration people actually use.

## Where the library is going

- **Performance.** Provers and verifiers as fast as the best production implementations, with every fast implementation proved equal to its specification.
- **Security.** Concrete soundness theorems as tight as the best known analyses, for any choice of field, extension, code rate, folding, queries and grinding, not for a handful of presets. As the analyses improve, the theorems follow.
- **Breadth.** Prime fields and binary fields, univariate and multilinear protocols, and polynomial commitments from FRI to WHIR, FLOCK and the next ones, adopted as they appear. No AIR, configuration or protocol is the goal; each one is an instance of the general machinery.
- **Built on its foundations.** Fields and polynomials come from [CompPoly](https://github.com/Verified-zkEVM/CompPoly), coding theory and protocol soundness from [ArkLib](https://github.com/Verified-zkEVM/ArkLib), cryptographic primitives from [VCVio](https://github.com/Verified-zkEVM/VCVio). Results that belong there are contributed there.

## North star for work in this repository

Use these to judge whether a change moves the library forward:

- **The general case is the target.** Implement and prove things for every field, extension, arity and configuration the construction supports. A result that holds for one field, one AIR or one parameter set is a step towards the general one, not a substitute for it.
- **Don't optimize for one showcase.** Benchmarks and examples (the Keccak AIR, a particular FRI configuration) are samples of the workloads we care about. A speedup or a tighter bound that only helps one of them is not worth its complexity; one that helps the general case is.
- **Prover and verifier both count.** So does the security analysis: a fast prover for a configuration whose security we can't state is half a result.
- **Build on the libraries instead of beside them.** Field arithmetic and polynomial kernels belong in CompPoly; coding theory, proximity gaps, IOPs and their soundness in ArkLib; hashes and oracle models in VCVio. Don't build a parallel version here; extend the library, and upstream what we prove.
- **Theorems say what they mean.** A hypothesis is a genuine assumption on the inputs, the configuration or an idealized primitive, and is visible in the statement. Never move part of the intended conclusion into a hypothesis, and never narrow a theorem to make its proof go through without saying so.
- **Keep up with the field.** When a better protocol or analysis appears, the library should adopt it rather than entrench what it has.
