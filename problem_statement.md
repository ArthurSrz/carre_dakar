# Le Carré de Dakar - Formal Problem Statement

## Problem Description

The "Carré de Dakar" is a mathematical puzzle defined as follows:

**Input:** A positive integer n (grid dimension)

**Goal:** Fill an n × n grid with:
- Natural numbers (positive integers)
- Arithmetic operators: +, -, ×, =
- Such that all arithmetic equations are valid

## Constraints

1. **Grid Structure:**
   - The grid is n × n where n > 3
   - Cells contain either numbers or operators
   - The equals sign (=) marks the end of equations

2. **Equation Validity:**
   - Both horizontal and vertical sequences form valid arithmetic equations
   - Equations follow the pattern: `number operator number operator ... = result`
   - Standard operator precedence applies (× before +/-)
   - All equations must evaluate to true

3. **Checkerboard Pattern Constraint:**
   - The grid follows a strict positional alternating pattern
   - Position (even_row, even_col): Must contain NUMBER
   - Position (even_row, odd_col): Must contain OPERATOR or EQUALS
   - Position (odd_row, odd_col): Must contain NUMBER
   - Position (odd_row, even_col): Must contain OPERATOR or EQUALS

   **Visual pattern:**
   ```
   N O N O N O N O N O
   O N O N O N O N O N
   N O N O N O N O N O
   O N O N O N O N O N
   ...
   ```

   **Equation implications:**
   - Even rows: NUM OP NUM OP NUM ... = RESULT
   - Odd rows: OP NUM OP NUM OP ... (often incomplete)
   - Even columns: NUM OP NUM OP NUM ... = RESULT
   - Odd columns: OP NUM OP NUM OP ... (often incomplete)

   Note: EQUALS (=) is treated as an OPERATOR for pattern purposes.

4. **Puzzle Mode:**
   - After generating a valid grid, hide certain numbers (replace with "?")
   - The hidden numbers should be uniquely determinable from the visible information

## Mathematical Question

**Theorem to Prove or Disprove:**

For all integers n > 3, there exists at least one valid configuration of the Carré de Dakar grid.

**Formal Statement:**

∀n ∈ ℕ, n > 3 ⟹ ∃ Grid(n) such that:
  - Grid(n) is an n × n matrix
  - Each cell contains either a natural number or an operator from {+, -, ×, =}
  - All horizontal and vertical equations in Grid(n) are arithmetically valid

## Example (from n=10 grid)

Row 1: 12 × 6 + 13 - ? = 6 × ?
Row 2: + 9 - ? × ? + ? = 6
...

## Complexity Analysis

This is a Constraint Satisfaction Problem (CSP) with:
- **Variables:** n² cells
- **Domain:** ℕ ∪ {+, -, ×, =}
- **Constraints:** Arithmetic validity for each equation

## Sub-questions

1. Does a solution always exist for n > 3?
2. What is the computational complexity of finding a solution?
3. How many solutions exist for a given n?
4. What is the optimal algorithm to generate valid grids?
5. Under what conditions is the puzzle (with hidden numbers) uniquely solvable?

## Related Problems

- KenKen puzzles
- Sudoku with arithmetic constraints
- Magic squares
- Cross-sums (Kakuro)
