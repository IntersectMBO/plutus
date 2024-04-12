---
title: "Introduction"
description: "A brief introduction to Plutus and its significance in the Cardano ecosystem"
date: 2024-03-12
---

# Section 1. Introduction

- Welcome to Plutus: A brief introduction to Plutus and its significance in the Cardano ecosystem.
- Target audience: 
	- Description of assumed knowledge (basic Haskell) and what the documentation aims to cover.
	- Identify the variety of primary roles we expect people to have who would be interested in the docs. 
- Document overview: Briefly outline the key sections and what developers will learn.

## Introductory resources
- Reference to the [Plutus Pioneer Program Gitbook](https://iog-academy.gitbook.io/plutus-pioneers-program-fourth-cohort/) (gitbook.io)
- Awareness of the Plutus Pioneer Program github page as a valuable resource: 
	- [https://github.com/input-output-hk/plutus-pioneer-program](https://github.com/input-output-hk/plutus-pioneer-program)
- Reference to the [IOG Academy Haskell Course](https://www.youtube.com/playlist?list=PLNEK_Ejlx3x1D9Vq5kqeC3ZDEP7in4dqb)
- IOG's technical community on Discord for PPP

> **Note** 
> 
> The draft outline above does not match the content below. At this stage, I've brought over the existing introduction so that everything is in one place. More editing is in the works. 

# Plutus Core

The Plutus project consists of Plutus Core, the programming language used for scripts on Cardano; tooling and compilers for compiling various intermediate languages into Plutus Core; and Plutus Tx, the compiler that compiles the Haskell source code into Plutus Core to form the on-chain part of a contract application. 
All of this is used in combination to write Plutus Core scripts that run on the Cardano blockchain.

This documentation introduces the Plutus Core programming language and programming with Plutus Tx. 
It includes explanations, tutorials, how-to instructions, troubleshooting, and reference information.

The intended audience of this documentation includes people who want to implement smart contracts on the Cardano blockchain. 
This involves using Plutus Tx to write scripts, requiring some knowledge of the Haskell programming language.

This guide is also meant for certification companies, certification auditors, and people who need an accurate specification. 
See, for example:

- the [Cardano Ledger Specification](https://github.com/IntersectMBO/cardano-ledger#cardano-ledger) and
- the [Plutus Core Specification](https://github.com/IntersectMBO/plutus#specifications-and-design).

# The Plutus repository

The [Plutus repository](https://github.com/IntersectMBO/plutus) contains the implementation, specification, and mechanized metatheory of Plutus Core. 
It also contains the Plutus Tx compiler and the libraries, such as `PlutusTx.List`, for writing Haskell code that can be compiled to Plutus Core.
