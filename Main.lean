import Mathlib
import Lean
import CellularAutomatas.ca
import CellularAutomatas.common
import CellularAutomatas.defs
import CellularAutomatas.find_some

open Lean Elab Command Term Meta

def main : IO Unit :=
  IO.println "Hello, Lean World!"
