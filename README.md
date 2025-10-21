# RISCV IOMMU FORMAL

This repository contains the **formal verification environment** for the [RISC-V IOMMU](https://github.com/zero-day-labs/riscv-iommu) design.


## License

This work is licensed under the Apache-2.0. See [LICENSE](./LICENSE) file for details.

## Table of Contents

- [Introduction](#introduction)
- [Repository Structure](#repository-structure)
- [Features](#features)
- [Verification Work Summary](#verification-work-summary)
- [Roadmap](#roadmap)

***


## Introduction

The RISC-V IOMMU architecture consists of two primary components:

1. **Address Translation Unit (ATU)** – Handles the translation of I/O virtual addresses (IOVA) to physical addresses based on the RISC-V IOMMU specification.  
2. **Software Interface Unit (SIU)** – Provides the configuration and control interface for system software to manage the IOMMU.

In this verification effort, the **focus is on the Address Translation Unit (ATU)**.  
The Software Interface Unit (SIU) is **black-boxed**, allowing the formal verification environment to concentrate on the correctness, consistency, and completeness of the translation logic.

The verification setup is built using **SystemVerilog Assertions (SVA)** and **Cadence JasperGold**, including a comprehensive set of assumptions, constraints, and cover properties to ensure exhaustive verification of translation behavior.

## **Repository Structure**

- **Documentation ([doc/](./doc/)):**
In the *doc* folder you can find various diagrams and graphical resources illustrating the internal design of the different components comprising the IOMMU IP.

- **Required SV headers ([include/](./include/)):**
SystemVerilog header files required to build the IP.

- **Required SV packages ([packages/](./packages/)):**
SystemVerilog packages used to build the IP.

- **RTL source files ([rtl/](./rtl/)):**
SystemVerilog source files that implement the IP, organized according to hardware blocks defined for the microarchitecture.

- **Standalone components ([vendor/](./vendor/)):**
The *vendor* folder holds SystemVerilog source files of all standalone RTL modules used in the IOMMU IP.

## **Features**

The following table lists all Verification features supported by this implementation, and those that may be included in the future.

| Feature | Notes | Status |
| ------------- | ------------- | ------------- |
| Verify Translation Logic | Translation of Virtual Address to Physical Address | Implemented |


## Verification Work Summary

The following components and functionalities were covered as part of the formal verification process:

- **Configuration**
  - Verification of register-level configurations and initialization sequences.
  - Ensured proper setup and access control for translation structures.

- **AXI Modeling for Interfaces**
  - Created formal AXI interface models for master/slave communication.
  - Modeled read/write transactions and response behavior for formal checks.

- **Verification of Caches (DDTC / PDTC)**
  - Verified data and page directory translation caches.
  - Checked cache entry allocation, eviction, and consistency properties.

- **Properties for CDW (Command/Data Write)**
  - Ensured correct ordering and completion of CDW operations.  
  - Verified command-data dependency and protocol compliance.

## Roadmap

Planned extensions and improvements to this formal verification environment include:

- [ ] **Integration of Software Interface Unit (SIU)** into the formal environment.  
- [ ] **Coverage closure** for remaining translation corner cases.  
- [ ] **Cross-check with simulation results** for mixed formal-simulation validation.  
- [ ] **Enhanced AXI protocol coverage** including burst and error scenarios.  
- [ ] **Automation scripts** for running proof, cover, and vacuity checks.  
- [ ] **Documentation and test plan publication** for reproducibility and review.

