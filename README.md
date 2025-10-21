# RISC-V IOMMU FORMAL

This repository contains the formal verification environment for the [Zero Day Labs RISC-V IOMMU](https://github.com/zero-day-labs/riscv-iommu) design.


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

The RISC-V IOMMU architecture consists of three primary components:

1. Translation Logic modules, which play a crucial role in the address translation process, enabling access to memory to locate data structures or caching context/translation data;
2. External interfaces, used by the IOMMU to interact with other hardware subsystems within the platform. 
3. Software interface modules, responsible for creating communication channels between the IOMMU hardware and software for specific purposes;

In this verification effort, the focus is on the **Translation Logic modules and External Interfaces**.  
The Software interface is **black-boxed**, allowing the formal verification environment to concentrate on the correctness, consistency, and completeness of the translation logic.

The verification setup is built using **SystemVerilog Assertions (SVA)** and **Cadence JasperGold**, including a comprehensive set of assumptions, constraints, and cover properties to ensure exhaustive verification of translation behavior.

## **Repository Structure**

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

- **AXI Modeling for Interfaces**
  - Modeled read/write transactions and response behavior for formal checks.

- **Verification of Caches (DDTC / PDTC)**
  - Verified insertion, invalidation, lookup, and replacement logic of device/process directory translation caches.

- **Properties for CDW**
  - Wrote properties to verify the accurate reporting of error messages during device directory walk(DDT) and process directory walk(PDT).
  
## Roadmap

Planned extensions and improvements to this formal verification environment include:

- [ ] **

