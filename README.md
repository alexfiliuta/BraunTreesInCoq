# Formal Verification of Braun Trees in Coq

This repository contains the formal verification of Braun Trees using the Coq proof assistant. The project defines the structure and operations of Braun Trees, ensuring the maintenance of invariants and adherence to algebraic and model-based specifications.

## Overview

Braun Trees are balanced binary trees that guarantee logarithmic performance in operations and are used as efficient implementation options for extensible arrays and priority queues. This project aims to provide a rigorous mathematical verification of Braun Tree operations using Coq, an interactive theorem prover.

## Repository Contents

- **Definitions**: Coq definition of Braun Trees.
- **Operations**: Implementation of Braun Tree operations such as lookup, insertion, and deletion.
- **Proofs**: Formal proofs ensuring that operations maintain tree invariants and adhere to algebraic and model-based specifications.

## Files

- `Definitions.v`: Contains the type definitions of Braun Trees along with the operations and the invariant.
- `HelperLemmas&FormalProofs.v`: Contains the implementation of the formal proofs along with the auxilliary lemmas.
- `Documentation`: The folder containing all relevant documentation including the proposal, the presentation and the report.

## Installation and Usage

1. **Install Coq**: Ensure you have Coq installed on your system. You can download it from the [Coq official website](https://coq.inria.fr/download).

2. **Clone the Repository**:
   ```bash
   git clone https://github.com/yourusername/BraunTreesInCoq.git
   ```
3. **Compile files using CoqIDE:**
   ```bash
   cd BraunTreesInCoq
   ```
   It is recommended to compile the files using CoqIDE for ease of use. Open CoqIDE, navigate to the 'Compile' menu, and select 'Make' to compile the project.
   Alternatively, you can generate a Makefile with:
   ```bash
   coq_makefile -f _CoqProject -o Makefile
   make
   ```
   
## License
This project is licensed under the MIT License - see the LICENSE.md file for details.
