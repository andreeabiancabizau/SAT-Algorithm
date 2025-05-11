# SAT Solver: DPLL, CDCL, DP, Resolution

## Overview

This project implements a SAT solver in Python, supporting four classical and modern techniques:
- **DPLL** (Davis–Putnam–Logemann–Loveland)
- **CDCL** (Conflict-Driven Clause Learning)
- **DP** (Davis–Putnam)
- **Resolution**

The solver allows for testing with:
- Standardized SAT benchmark files in DIMACS CNF format
- Custom logical formulas entered manually

It also includes memory and time measurement for each solving method.

---

## Features

- Supports both satisfiable and unsatisfiable formulas
- Step-by-step tracing and verbose modes for each algorithm
- Tracks peak memory usage (in KB) and execution time (in seconds)
- User-friendly menu-based interface
- Compatibility with `.cnf` files from benchmark datasets like SATLIB

---

## Installation

### 1. Save the code 
### 2. Ensure you have Python 3.8+ installed and install sympy pycosat

---
## Running the Program 

Put it in your IDE or in your terminal and you will be prompted with a menu: 
1. Use benchmark (.cnf file)
2. Enter your own logical formula
3. How to use

Option 1: Using .cnf Benchmark Files
	1.	Download CNF files from the SATLIB Benchmark Collection.
	2.	Place the .cnf files in the same directory as SAT.py.
	3.	Select option 1 and input the file path.

 Option 2: Entering a Custom Formula

Input a logical formula using the syntax described in the "How to use" menu. 
Important: Do not use the letters E, I, or O as variables (they are reserved in SymPy).
---
## Output

For each method, the program will print:
	•	Satisfiability result: SAT or UNSAT
	•	Execution time
	•	Peak memory usage


