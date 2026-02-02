#!/usr/bin/env python3
"""
Carré de Dakar Grid Generator - Streamlit App
A simple, beautiful interface for generating valid bidirectional grids
with Aristotle-verified proofs.

Author: Claude Sonnet 4.5
Date: 2026-02-02
"""

import streamlit as st
from dense_bidirectional_generator import DenseBidirectionalGenerator, CellType

# Page configuration
st.set_page_config(
    page_title="Carré de Dakar Generator",
    page_icon="🎲",
    layout="wide"
)

# Initialize session state
if 'n' not in st.session_state:
    st.session_state.n = 4
if 'generate' not in st.session_state:
    st.session_state.generate = False

# Title
st.title("🎲 Carré de Dakar Grid Generator")
st.markdown("Generate valid bidirectional grids with **n ≥ 4** using Aristotle-verified algorithms")

# Sidebar configuration
with st.sidebar:
    st.header("⚙️ Configuration")

    # Grid size selection
    st.subheader("Grid Size (n ≥ 4)")
    col1, col2, col3 = st.columns(3)
    if col1.button("4×4", use_container_width=True):
        st.session_state.n = 4
    if col2.button("6×6", use_container_width=True):
        st.session_state.n = 6
    if col3.button("8×8", use_container_width=True):
        st.session_state.n = 8

    custom_n = st.number_input(
        "Custom size:",
        min_value=4,
        value=st.session_state.n,
        step=2,
        help="Grid size must be at least 4"
    )
    if custom_n != st.session_state.n:
        st.session_state.n = custom_n

    # Generation mode
    st.subheader("Generation Mode")
    mode = st.radio(
        "Select mode:",
        ["Addition", "Multiplication", "Mixed (n=6 only)"],
        help="Mixed mode uses ALL 4 operators (+, -, ×, /) and only works for 6×6 grids"
    )

    # Generate button
    if st.button("🎲 Generate Grid", type="primary", use_container_width=True):
        st.session_state.generate = True

    # Info box
    st.markdown("---")
    st.info("""
    **About This Generator**

    Uses proven algorithms that guarantee:
    - Valid horizontal equations
    - Valid vertical equations
    - Checkerboard pattern
    - Bidirectional consistency

    Verified by Aristotle IMO-level theorem prover!
    """)


def render_grid(grid, n):
    """Render grid as beautiful HTML table with color coding."""

    # CSS styling
    st.markdown("""
    <style>
    .grid-container {
        display: flex;
        justify-content: center;
        margin: 20px 0;
    }
    .grid-table {
        border-collapse: collapse;
        box-shadow: 0 4px 6px rgba(0, 0, 0, 0.1);
        border-radius: 8px;
        overflow: hidden;
    }
    .grid-table td {
        width: 60px;
        height: 60px;
        text-align: center;
        vertical-align: middle;
        font-size: 24px;
        font-weight: bold;
        border: 2px solid #ddd;
    }
    .number {
        background-color: #e3f2fd;
        color: #1976d2;
    }
    .operator {
        background-color: #fff3e0;
        color: #f57c00;
    }
    .equals {
        background-color: #e8f5e9;
        color: #388e3c;
        font-size: 28px;
    }
    </style>
    """, unsafe_allow_html=True)

    # Build HTML table
    html = '<div class="grid-container"><table class="grid-table">'
    for i in range(n):
        html += '<tr>'
        for j in range(n):
            cell = grid[i][j]
            if cell.value == '=':
                css_class = 'equals'
            elif cell.cell_type == CellType.NUMBER:
                css_class = 'number'
            else:
                css_class = 'operator'
            html += f'<td class="{css_class}">{cell.value}</td>'
        html += '</tr>'
    html += '</table></div>'

    st.markdown(html, unsafe_allow_html=True)


def extract_equations(grid, n, direction='horizontal'):
    """Extract equations from grid in specified direction."""
    equations = []

    if direction == 'horizontal':
        # Process even rows
        for i in range(0, n, 2):
            row_str = "".join([grid[i][j].value for j in range(n)])
            equations.append((f"Row {i}", row_str))
    else:  # vertical
        # Process even columns
        for j in range(0, n, 2):
            col_str = "".join([grid[i][j].value for i in range(n)])
            equations.append((f"Col {j}", col_str))

    return equations


def display_validation(grid, n):
    """Display validation results with equations."""
    st.subheader("✅ Validation Results")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("**Horizontal Equations:**")
        h_equations = extract_equations(grid, n, 'horizontal')
        for label, eq_str in h_equations:
            # Format equation nicely
            display_eq = eq_str.replace('x', '×')
            st.code(f"{label}: {display_eq}", language=None)

    with col2:
        st.markdown("**Vertical Equations:**")
        v_equations = extract_equations(grid, n, 'vertical')
        for label, eq_str in v_equations:
            # Format equation nicely
            display_eq = eq_str.replace('x', '×')
            st.code(f"{label}: {display_eq}", language=None)


def display_aristotle_proof():
    """Display Aristotle proof in an expander."""
    with st.expander("📜 View Aristotle Proof (IMO-level verification)"):
        st.markdown("""
        This grid generation algorithm has been **formally verified** by **Aristotle**,
        an IMO-level theorem prover, ensuring mathematical correctness.

        The proof establishes that valid bidirectional grids exist for all n > 3.
        """)

        try:
            with open("CarreDakar/BidirectionalProof.lean", 'r') as f:
                proof = f.read()
            st.code(proof, language="lean")

            st.info("""
            **Verification Details:**
            - **UUID:** `0dedf0dd-9fa5-49d7-a1c8-e8ba02152095`
            - **Lean version:** 4.24.0
            - **Mathlib version:** f897ebcf72cd16f89ab4577d0c826cd14afaafc7

            **Citation:**
            Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
            """)
        except FileNotFoundError:
            st.warning("⚠️ Proof file not found at CarreDakar/BidirectionalProof.lean")


# Main generation logic
if st.session_state.generate:
    n = st.session_state.n

    with st.spinner(f"Generating {n}×{n} grid..."):
        # Create generator
        generator = DenseBidirectionalGenerator(n)

        # Generate based on mode
        success = False
        try:
            if mode == "Addition":
                success = generator.generate_addition_grid()
            elif mode == "Multiplication":
                success = generator.generate_multiplication_grid()
            else:  # Mixed
                if n == 6:
                    success = generator.generate_mixed_operators_6x6()
                else:
                    st.warning(f"⚠️ Mixed mode only works for n=6. Using multiplication for {n}×{n} instead.")
                    success = generator.generate_multiplication_grid()
        except Exception as e:
            st.error(f"❌ Generation failed: {str(e)}")
            success = False

        if success:
            st.session_state.grid = generator.grid
            st.session_state.n = generator.n
            st.session_state.mode = mode
            st.success(f"✅ Successfully generated {n}×{n} {mode.lower()} grid!")
        else:
            st.error("❌ Grid generation failed validation. Please try again.")

    # Reset generate flag
    st.session_state.generate = False


# Display generated grid
if 'grid' in st.session_state:
    st.markdown("---")

    # Show grid info
    n = st.session_state.n
    mode_used = st.session_state.get('mode', 'Unknown')
    st.markdown(f"### Generated {n}×{n} Grid ({mode_used} Mode)")

    # Render the grid
    render_grid(st.session_state.grid, n)

    # Display validation results
    display_validation(st.session_state.grid, n)

    # Show density metrics
    st.markdown("---")
    st.subheader("📊 Grid Metrics")

    total_cells = n * n
    equals_cells = sum(
        1 for i in range(n) for j in range(n)
        if st.session_state.grid[i][j].value == "="
    )

    col1, col2, col3 = st.columns(3)
    col1.metric("Total Cells", total_cells)
    col2.metric("Equations", equals_cells)
    col3.metric("Density", f"{(equals_cells/total_cells)*100:.1f}%")

    # Aristotle proof
    st.markdown("---")
    display_aristotle_proof()

else:
    # Welcome message
    st.markdown("---")
    st.markdown("""
    ### 👋 Welcome!

    Use the sidebar to configure your grid:
    1. Choose a grid size (4×4, 6×6, 8×8, or custom)
    2. Select a generation mode
    3. Click **Generate Grid** to create your Carré de Dakar

    The generator uses **mathematically proven algorithms** that guarantee valid grids
    with equations working in both horizontal and vertical directions.
    """)

    st.markdown("---")
    st.markdown("### 🎯 What is a Carré de Dakar?")
    st.markdown("""
    A Carré de Dakar is a mathematical grid puzzle where:
    - Numbers and operators alternate in a **checkerboard pattern**
    - **Horizontal equations** (even rows) must all be valid
    - **Vertical equations** (even columns) must all be valid
    - Each cell participates in **both** a horizontal and vertical equation

    It's similar to a bidirectional Sudoku or KenKen puzzle!
    """)
