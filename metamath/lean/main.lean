import system.io
import init.data.string.ops

inductive stmt : Type
| constant_stmt : list string -> stmt
| variable_stmt : list string -> stmt
| floating_stmt : string -> string -> string -> stmt
| essential_stmt : string -> string -> (list string) -> stmt
| axiom_stmt : string -> string -> (list string) -> stmt
| provable_stmt : string -> string -> (list string) -> (list string) -> stmt
| parse_error

def stmt_to_string : stmt -> string
| (stmt.constant_stmt l) := "constant_stmt: " ++ (list.to_string l)
| (stmt.variable_stmt l) := "variable_stmt: " ++ (list.to_string l)
| (stmt.floating_stmt name typecode var) := "floating_stmt: " ++ name ++ " " ++ typecode ++ " " ++ var
| (stmt.essential_stmt name typecode ms) := "essential_stmt: " ++ name ++ " " ++ typecode ++ " " ++ (list.to_string ms)
| (stmt.axiom_stmt name typecode ms) := "axiom_stmt: " ++ name ++ " " ++ typecode ++ " " ++ (list.to_string ms)
| (stmt.provable_stmt name typecode ms proof) := "provable_stmt: " ++ name ++ " " ++ typecode ++ " " ++ (list.to_string ms) ++ " " ++ (list.to_string proof)
| stmt.parse_error := "PARSE ERROR"

instance : has_to_string stmt := ⟨stmt_to_string⟩

def good (s : string) : string -> bool
| "$." := true
| default := false

def consume_until (s : string) : list string -> (list string) × (list string)
| [] := ([], [])
| (a :: l) := if a ≠ s then let (aa, bb) := consume_until l in (a :: aa, bb) else ([], l)

def parser : list string -> list stmt
| ("$c" :: l) := let (consts, rest) := consume_until "$." l in [stmt.constant_stmt consts]
| ("$v" :: l) := [stmt.variable_stmt l]
| default := [stmt.parse_error]

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
