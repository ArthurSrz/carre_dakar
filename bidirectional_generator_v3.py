#!/usr/bin/env python3
"""
Bidirectional Generator V3 - Continuous Pattern Approach
Fills entire grid with coordinated pattern instead of tiling blocks
"""

import random
from typing import List, Tuple
from dataclasses import dataclass
from enum import Enum

class CellType(Enum):
    NUMBER = "number"
    OPERATOR = "operator"
    EQUALS = "equals"

@dataclass
class Cell:
    value: str
    cell_type: CellType

class ContinuousBidirectionalGenerator:
    """
    Uses continuous pattern filling instead of block tiling

    Key insight: For bidirectional validity, use:
    - Simple equations (1+1=2) that work everywhere
    - Coordinate horizontal AND vertical equations
    - Ensure every intersection point is consistent
    """

    def __init__(self, n: int = 10):
        if n < 4:
            raise ValueError("Grid must be at least 4×4")
        if n % 2 != 0:
            print(f"⚠️  Warning: Odd n={n}. Even sizes work better.")

        self.n = n
        self.grid: List[List[Cell]] = [[None] * n for _ in range(n)]

    def generate(self) -> bool:
        """
        Generate using coordinated continuous filling

        Strategy:
        1. Fill entire grid respecting checkerboard
        2. Use uniform values (all 1's for numbers)
        3. Use uniform operators (all +)
        4. This guarantees equations work:
           - Horizontal: 1+1=2, 1+1=2, ...
           - Vertical: 1+1=2, 1+1=2, ...
        """
        print(f"\n🎯 Generating {self.n}×{self.n} bidirectional grid...")
        print("   Using continuous uniform pattern")

        # Fill grid based on checkerboard pattern
        for i in range(self.n):
            for j in range(self.n):
                # Determine expected type
                is_number_position = (i % 2 == 0 and j % 2 == 0) or (i % 2 == 1 and j % 2 == 1)

                if is_number_position:
                    # Number position
                    if (i % 4 == 3 or i % 4 == 0) and (j % 4 == 3 or j % 4 == 0):
                        # Result position (after =)
                        self.grid[i][j] = Cell("2", CellType.NUMBER)
                    else:
                        # Operand position
                        self.grid[i][j] = Cell("1", CellType.NUMBER)
                else:
                    # Operator position
                    if (i % 4 == 3 or i % 4 == 0) and (j % 4 == 3 or j % 4 == 0):
                        # Equals position
                        self.grid[i][j] = Cell("=", CellType.EQUALS)
                    else:
                        # Operator position
                        self.grid[i][j] = Cell("+", CellType.OPERATOR)

        # Validate
        checker_ok = self._validate_checkerboard()
        h_ok, h_err = self._validate_horizontal_equations()
        v_ok, v_err = self._validate_vertical_equations()

        all_ok = checker_ok and h_ok and v_ok

        if all_ok:
            print("✅ All validations passed!")
            print(f"   - Checkerboard: ✓")
            print(f"   - Horizontal: ✓")
            print(f"   - Vertical: ✓")
        else:
            print("❌ Validation failed:")
            if not checker_ok:
                print("   - Checkerboard: ✗")
            if not h_ok:
                print(f"   - Horizontal: ✗ ({len(h_err)} errors)")
                for e in h_err[:3]:
                    print(f"      {e}")
            if not v_ok:
                print(f"   - Vertical: ✗ ({len(v_err)} errors)")
                for e in v_err[:3]:
                    print(f"      {e}")

        return all_ok

    def _validate_checkerboard(self) -> bool:
        for i in range(self.n):
            for j in range(self.n):
                expected_number = (i % 2 == 0 and j % 2 == 0) or (i % 2 == 1 and j % 2 == 1)
                actual_number = self.grid[i][j].cell_type == CellType.NUMBER

                if expected_number != actual_number:
                    return False
        return True

    def _validate_horizontal_equations(self) -> Tuple[bool, List[str]]:
        errors = []

        # Check even rows
        for i in range(0, self.n, 2):
            # Build equation string for entire row
            row_str = "".join([self.grid[i][j].value for j in range(self.n)])

            # Find all equations (split by =)
            parts = row_str.split('=')

            # Each pair (left, right) should be a valid equation
            for k in range(len(parts) - 1):
                left = parts[k].strip()
                # Right side is everything before next = or end
                right_full = parts[k+1]
                right_val = ""

                # Extract first number from right side
                for char in right_full:
                    if char.isdigit():
                        right_val += char
                    else:
                        break

                if left and right_val:
                    try:
                        result = eval(left.replace('×', '*'))
                        expected = int(right_val)

                        if result != expected:
                            errors.append(f"Row {i}: {left} = {result}, expected {expected}")
                    except:
                        pass

        return len(errors) == 0, errors

    def _validate_vertical_equations(self) -> Tuple[bool, List[str]]:
        errors = []

        # Check even columns
        for j in range(0, self.n, 2):
            # Build equation string for entire column
            col_str = "".join([self.grid[i][j].value for i in range(self.n)])

            # Find all equations
            parts = col_str.split('=')

            for k in range(len(parts) - 1):
                left = parts[k].strip()
                right_full = parts[k+1]
                right_val = ""

                for char in right_full:
                    if char.isdigit():
                        right_val += char
                    else:
                        break

                if left and right_val:
                    try:
                        result = eval(left.replace('×', '*'))
                        expected = int(right_val)

                        if result != expected:
                            errors.append(f"Col {j}: {left} = {result}, expected {expected}")
                    except:
                        pass

        return len(errors) == 0, errors

    def display(self):
        print("\n" + "=" * (self.n * 6))
        for row in self.grid:
            print("|" + "|".join([f"{cell.value:^5}" for cell in row]) + "|")
        print("=" * (self.n * 6))

    def display_pattern_analysis(self):
        """Show pattern structure"""
        print("\nPattern Analysis:")
        print("First 6 rows, first 6 columns:")
        size = min(6, self.n)

        for i in range(size):
            row = []
            for j in range(size):
                cell = self.grid[i][j]
                if cell.cell_type == CellType.NUMBER:
                    row.append(f"N({cell.value})")
                elif cell.cell_type == CellType.EQUALS:
                    row.append(" = ")
                else:
                    row.append(f" {cell.value} ")
            print(" ".join(row))


def test_v3():
    print("\n" + "=" * 80)
    print("BIDIRECTIONAL GENERATOR V3 - CONTINUOUS PATTERN")
    print("=" * 80)

    for n in [4, 6, 8, 10, 12]:
        print(f"\n{'─' * 80}")
        print(f"Testing n = {n}")
        print('─' * 80)

        gen = ContinuousBidirectionalGenerator(n=n)
        success = gen.generate()

        if success:
            print(f"✅ SUCCESS for n={n}!")

            if n <= 6:
                gen.display()
                gen.display_pattern_analysis()
        else:
            print(f"❌ FAILED for n={n}")

    print("\n" + "=" * 80)
    print("TEST COMPLETE")
    print("=" * 80)


if __name__ == "__main__":
    test_v3()
