import system.io
import init.data.string.ops

inductive stmt : Type
| constant_stmt : list string -> stmt

def stmt_to_string : stmt -> string
| (stmt.constant_stmt l) := "constant_stmt: " ++ (list.to_string l)

instance : has_to_string stmt := ⟨stmt_to_string⟩

/-
structure constant_stmt extends stmt :=
mk :: (consts : list string)


structure variable_stmt extends stmt :=
mk :: (vars : list string)

structure named_stmt extends stmt :=
mk :: (name : string)

structure floating_stmt extends named_stmt :=
mk :: (typecode : string) (var : string) 

structure axiom_stmt extends named_stmt :=
mk :: (typecode : string) (ss : list string)

structure provable_stmt extends named_stmt :=
mk :: (typecode : string) (ss : list string) (proof : list string)

def parser : list string -> stmt
| [] := []
| ["$c"::l] := (stmt.constant_stmt l)
-/

def parser : list string -> list stmt
| [] := []
| [a] := []
| ("$c" :: l) := [stmt.constant_stmt l]
| (a :: b) := []

def whitespace : char -> bool
| ' ' := true
| '\n' := true
| default := false

def lexer (s : string) : list string :=
  ((s.split) whitespace).filter (λ r, r ≠ "")

-- IO crap below this line
open io

def get_file : io char_buffer :=
    fs.read_file "/Users/smooth/build/twitchcoq/metamath/simple.mm"

def main : io unit :=
do a <- get_file,
   let s := a.to_string,
   let l := lexer s,
   let p := parser l,
   put_str ((list.to_string p) ++ "\n")
   --put_str ((list.to_string l) ++ "\n" ++ (list.to_string p) ++ "\n")

#eval main
