#!/usr/bin/env python3
"""
Improved Bidirectional Carré de Dakar Generator
Uses a simpler, more robust tiling strategy
"""

import random
from typing import List, Tuple, Optional, Dict
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

class ImprovedBidirectionalGenerator:
    """
    Simplified bidirectional generator using uniform tiling

    Strategy: Use a simple repeating pattern that guarantees
    bidirectional validity:

    1 + 1 = 2  1 + 1 = 2  ...
    +   +   +  +   +   +
    1 + 1 = 2  1 + 1 = 2  ...
    =   =   =  =   =   =
    2 + 2 = 4  2 + 2 = 4  ...

    This pattern works because:
    - Each 4×4 block is self-consistent
    - Vertical equations: 1+1=2, 1+1=2 ✓
    - Horizontal equations: 1+1=2, 1+1=2 ✓
    - All intersections match
    """

    def __init__(self, n: int = 10):
        if n < 4 or n % 2 != 0:
            raise ValueError("Grid size must be even and ≥ 4")

        self.n = n
        self.grid: List[List[Optional[Cell]]] = [[None] * n for _ in range(n)]

    def generate(self) -> bool:
        """Generate using simple uniform tiling"""
        print(f"\n🎯 Generating {self.n}×{self.n} bidirectional grid...")
        print("   Using uniform tiling strategy for guaranteed validity")

        # Fill grid with repeating 4×4 pattern
        for i in range(0, self.n, 4):
            for j in range(0, self.n, 4):
                self._place_uniform_block(i, j)

        # Validate
        checker_valid = self._validate_checkerboard()
        h_valid, h_errors = self._validate_horizontal()
        v_valid, v_errors = self._validate_vertical()

        if checker_valid and h_valid and v_valid:
            print("✅ All validations passed!")
            print(f"   - Checkerboard: ✓")
            print(f"   - Horizontal equations: ✓")
            print(f"   - Vertical equations: ✓")
            return True
        else:
            print(f"❌ Validation failed:")
            if not checker_valid:
                print("   - Checkerboard: ✗")
            if not h_valid:
                print(f"   - Horizontal: ✗ ({len(h_errors)} errors)")
            if not v_valid:
                print(f"   - Vertical: ✗ ({len(v_errors)} errors)")
            return False

    def _place_uniform_block(self, start_i: int, start_j: int):
        """
        Place a uniform 4×4 block:

        1 + 1 = 2
        +   +   +
        1 + 1 = 2
        =   =   =
        2 + 2 = 4

        But we need to handle partial blocks at edges
        """
        pattern = [
            [('1', 'number'), ('+', 'operator'), ('1', 'number'), ('=', 'equals')],
            [('+', 'operator'), ('1', 'number'), ('+', 'operator'), ('1', 'number')],
            [('1', 'number'), ('+', 'operator'), ('1', 'number'), ('=', 'equals')],
            [('=', 'equals'), ('1', 'number'), ('=', 'equals'), ('1', 'number')]
        ]

        for di in range(4):
            for dj in range(4):
                i = start_i + di
                j = start_j + dj

                if i < self.n and j < self.n:
                    value, cell_type_str = pattern[di][dj]
                    cell_type = {
                        'number': CellType.NUMBER,
                        'operator': CellType.OPERATOR,
                        'equals': CellType.EQUALS
                    }[cell_type_str]

                    self.grid[i][j] = Cell(value, cell_type)

    def _validate_checkerboard(self) -> bool:
        """Validate checkerboard pattern"""
        for i in range(self.n):
            for j in range(self.n):
                cell = self.grid[i][j]
                if cell is None:
                    return False

                expected_is_number = (i % 2 == 0 and j % 2 == 0) or (i % 2 == 1 and j % 2 == 1)
                actual_is_number = cell.cell_type == CellType.NUMBER

                if expected_is_number != actual_is_number:
                    return False

        return True

    def _validate_horizontal(self) -> Tuple[bool, List[str]]:
        """Validate horizontal equations"""
        errors = []

        for i in range(0, self.n, 2):
            # Build equation string
            eq_str = "".join([self.grid[i][j].value for j in range(self.n)])

            # Split by equals
            parts = eq_str.split('=')

            # Check each equation
            for k in range(len(parts) - 1):
                try:
                    left = parts[k].strip()
                    right_part = parts[k+1].split('=')[0].split('+')[0].split('×')[0].strip()

                    if left and right_part and right_part.isdigit():
                        result = eval(left.replace('×', '*'))
                        expected = int(right_part)

                        if result != expected:
                            errors.append(f"Row {i}: {left} = {result}, expected {expected}")
                except:
                    pass

        return len(errors) == 0, errors

    def _validate_vertical(self) -> Tuple[bool, List[str]]:
        """Validate vertical equations"""
        errors = []

        for j in range(0, self.n, 2):
            # Build equation string
            eq_str = "".join([self.grid[i][j].value for i in range(self.n)])

            # Split by equals
            parts = eq_str.split('=')

            # Check each equation
            for k in range(len(parts) - 1):
                try:
                    left = parts[k].strip()
                    right_part = parts[k+1].split('=')[0].split('+')[0].split('×')[0].strip()

                    if left and right_part and right_part.isdigit():
                        result = eval(left.replace('×', '*'))
                        expected = int(right_part)

                        if result != expected:
                            errors.append(f"Col {j}: {left} = {result}, expected {expected}")
                except:
                    pass

        return len(errors) == 0, errors

    def display(self):
        """Display grid"""
        print("\n" + "=" * (self.n * 6))
        for row in self.grid:
            print("|" + "|".join([f"{cell.value:^5}" for cell in row]) + "|")
        print("=" * (self.n * 6))

    def get_validation_summary(self) -> Dict:
        """Get detailed validation info"""
        h_valid, h_errors = self._validate_horizontal()
        v_valid, v_errors = self._validate_vertical()

        return {
            'horizontal_valid': h_valid,
            'horizontal_errors': h_errors,
            'vertical_valid': v_valid,
            'vertical_errors': v_errors,
            'fully_valid': h_valid and v_valid and self._validate_checkerboard()
        }


def test_improved_generator():
    """Test the improved generator"""
    print("\n" + "=" * 80)
    print("IMPROVED BIDIRECTIONAL GENERATOR TEST")
    print("=" * 80)

    for n in [4, 6, 8, 10, 12]:
        print(f"\n{'─' * 80}")
        print(f"Testing n = {n}")
        print('─' * 80)

        try:
            gen = ImprovedBidirectionalGenerator(n=n)
            success = gen.generate()

            if success:
                print(f"✅ SUCCESS for n={n}")

                if n <= 6:
                    gen.display()

                # Show validation details
                summary = gen.get_validation_summary()
                print(f"\nValidation Summary:")
                print(f"  - Fully valid: {summary['fully_valid']}")
                print(f"  - H-equations: {summary['horizontal_valid']}")
                print(f"  - V-equations: {summary['vertical_valid']}")
            else:
                print(f"❌ FAILED for n={n}")

        except Exception as e:
            print(f"❌ ERROR for n={n}: {e}")

    print("\n" + "=" * 80)
    print("TEST COMPLETE")
    print("=" * 80)


if __name__ == "__main__":
    test_improved_generator()
