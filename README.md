# RISC-V IOMMU FORMAL

This repository contains the formal verification environment for the [Zero Day Labs RISC-V IOMMU](https://github.com/zero-day-labs/riscv-iommu) design.


## License

This work is licensed under the Apache-2.0. See [LICENSE](./LICENSE) file for details.

## Table of Contents

- [Introduction](#introduction)
- [Repository Structure](#repository-structure)
- [Verification Work Summary](#verification-work-summary)
- [Roadmap](#roadmap)

***


## Introduction

The RISC-V IOMMU consists of three primary components:

1. **Translation Logic** modules, which play a crucial role in the address translation process, enabling access to memory to locate data structures or caching context/translation data;
2. **External interfaces**, used by the IOMMU to interact with other hardware subsystems within the platform.
3. **Software interface** modules, responsible for creating communication channels between the IOMMU hardware and software for specific purposes;

In this verification effort, the focus is on the **Translation Logic modules and External Interfaces**. The Software interface is **black-boxed**, allowing the formal verification environment to concentrate on the correctness, consistency, and completeness of the translation logic.
## **Repository Structure**

- **Bind file ([bind](./formal/bind/)):**
Contains the SystemVerilog bind file used to connect the FPV environment with the RTL.

- **Scripts ([script](./formal/script/)):**
Includes scripts used to run the testbench (TB) on JasperGold 2019.

- **SVA ([sva](./formal/sva/)):**
SystemVerilog files that contains the verification of the translation logic modules and modelling of input signals

- **cut_point_assumptions ([cut_point_assumptions](./formal/sva/cut_point_assumptions/)):**
SystemVerilog file that contains the signals that were cutpointed

## Verification Work Summary

The following components and functionalities were covered as part of the formal verification process:

- **AXI Modeling for Interfaces**
  - Modeled read/write transactions and response behavior for formal checks.

- **Cache Verification (DDTC / PDTC / IOTLB)**
  - Verified insertion, invalidation, lookup, and replacement logic of IOMMU Address Translation Cache(IOATC).

- **Properties for Memory Walk**
  - Wrote properties to verify the accurate reporting of error messages during Device Directory Walk(DDW), Process Directory Walk(PDW) and Page Table Walk(PTW).

## Roadmap

Planned extensions and improvements to this formal verification environment include:

- [ ] Continued development and optimization of the Formal Verification IP (FVIP).
- [ ] Completion of the AXI modeling, which is currently 70% implemented.
- [ ] Although the existing properties have already detected 20+ bugs, further refinement is possible - especially when applied to a more stable RTL version.
