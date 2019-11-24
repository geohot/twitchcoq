import system.io
import init.data.string.ops

inductive stmt : Type
| constant_stmt : list string -> stmt
| variable_stmt : list string -> stmt
| disjoint_stmt : list string -> stmt
| floating_stmt : string -> string -> string -> stmt
| essential_stmt : string -> string -> (list string) -> stmt
| axiom_stmt : string -> string -> (list string) -> stmt
| provable_stmt : string -> string -> (list string) -> (list string) -> stmt
| scope_stmt : (list stmt) -> stmt
| scope_open : stmt
| scope_close : stmt
| parse_error : (list string) -> stmt

def stmt_to_string : stmt -> string
| (stmt.constant_stmt l) := "constant_stmt: " ++ (list.to_string l)
| (stmt.variable_stmt l) := "variable_stmt: " ++ (list.to_string l)
| (stmt.disjoint_stmt l) := "disjoint_stmt: " ++ (list.to_string l)
| (stmt.floating_stmt name typecode var) := "floating_stmt: " ++ name ++ " " ++ typecode ++ " " ++ var
| (stmt.essential_stmt name typecode ms) := "essential_stmt: " ++ name ++ " " ++ typecode ++ " " ++ (list.to_string ms)
| (stmt.axiom_stmt name typecode ms) := "axiom_stmt: " ++ name ++ " " ++ typecode ++ " " ++ (list.to_string ms)
| (stmt.provable_stmt name typecode ms proof) := "provable_stmt: " ++ name ++ " " ++ typecode ++ " " ++ (list.to_string ms) ++ " " ++ (list.to_string proof)
| (stmt.scope_open) := "scope_open"
| (stmt.scope_close) := "scope_close"
| (stmt.scope_stmt lst) := "scope_stmt: TODO"
| (stmt.parse_error lst) := "PARSE ERROR: " ++ (lst.take 10).to_string

instance : has_to_string stmt := ⟨stmt_to_string⟩

def consume_until (s : string) : list string -> (list string) × (list string)
| [] := ([], [])
| (a :: l) := if a ≠ s then let (aa, bb) := consume_until l in (a :: aa, bb) else ([], l)

def parser_core : nat -> list string -> list stmt
| 0 := λ x, [(stmt.parse_error x)]
| (n+1) := let pc := (parser_core n) in λ x, match x with
    | ("$c" :: l) := let (x, rest) := consume_until "$." l in (stmt.constant_stmt x) :: (pc rest)
    | ("$v" :: l) := let (x, rest) := consume_until "$." l in (stmt.variable_stmt x) :: (pc rest)
    | ("$d" :: l) := let (x, rest) := consume_until "$." l in (stmt.disjoint_stmt x) :: (pc rest)
    | (name :: "$f" :: typecode :: var :: "$." :: l) := (stmt.floating_stmt name typecode var) :: (pc l)
    | (name :: "$e" :: typecode :: l) := let (x, rest) := consume_until "$." l in
        (stmt.essential_stmt name typecode x) :: (pc rest) 
    | (name :: "$a" :: typecode :: l) := let (x, rest) := consume_until "$." l in
        (stmt.axiom_stmt name typecode x) :: (pc rest) 
    | (name :: "$p" :: typecode :: l) := let (x, rest) := consume_until "$=" l in
        let (y, rest2) := consume_until "$." rest in
            (stmt.provable_stmt name typecode x y) :: (pc rest2) 
    -- TODO: fix scope statements to be properly nested
    --| ("${" :: l) := let (x, rest) := consume_until "$}" l in
    --    (stmt.scope_stmt ((parser_core n) x)) :: (pc rest) 
    | ("${" :: l) := (stmt.scope_open) :: (pc l)
    | ("$}" :: l) := (stmt.scope_close) :: (pc l)
    | ("$(" :: l) := let (x, rest) := consume_until "$)" l in (pc rest) 
    | [] := []
    | l := [(stmt.parse_error l)]
    end

def parser (s : list string) : list stmt := ((parser_core s.length) s)

def whitespace : char -> bool
| ' ' := true
| '\n' := true
| default := false

def lexer (s : string) : list string :=
  ((s.split) whitespace).filter (λ r, r ≠ "")

-- IO crap below this line
open io

def get_file : io char_buffer :=
    fs.read_file "/Users/smooth/build/twitchcoq/metamath/lib/peano.mm"

def main : io unit :=
do a <- get_file,
   let s := a.to_string,
   let l := lexer s,
   let p := parser l,
   put_str ((p.foldl (λ r s, r ++ "\n" ++ (stmt_to_string s)) "PARSE LIST") ++ "\n")
   --put_str ((list.to_string l) ++ "\n" ++ (list.to_string p) ++ "\n")

#eval main
