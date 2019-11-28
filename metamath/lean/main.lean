import system.io

open list
open string

inductive stmt : Type
| constant_stmt : list string -> stmt
| variable_stmt : list string -> stmt
| disjoint_stmt : list string -> stmt
| floating_stmt : string -> string -> string -> stmt
| essential_stmt : string -> string -> (list string) -> stmt
| axiom_stmt : string -> string -> (list string) -> stmt
| provable_stmt : string -> string -> (list string) -> (list string) -> stmt
| scope_stmt : (list stmt) -> stmt
| include_stmt : string -> stmt
| parse_error : (list string) -> stmt

def stmt_to_string : stmt -> string
| (stmt.constant_stmt l) := "constant_stmt: " ++ (list.to_string l)
| (stmt.variable_stmt l) := "variable_stmt: " ++ (list.to_string l)
| (stmt.disjoint_stmt l) := "disjoint_stmt: " ++ (list.to_string l)
| (stmt.floating_stmt name typecode var) := "floating_stmt: " ++ name ++ " " ++ typecode ++ " " ++ var
| (stmt.essential_stmt name typecode ms) := "essential_stmt: " ++ name ++ " " ++ typecode ++ " " ++ (list.to_string ms)
| (stmt.axiom_stmt name typecode ms) := "axiom_stmt: " ++ name ++ " " ++ typecode ++ " " ++ (list.to_string ms)
| (stmt.provable_stmt name typecode ms proof) := "provable_stmt: " ++ name ++ " " ++ typecode ++ " " ++ (list.to_string ms) ++ " " ++ (list.to_string proof)
| (stmt.scope_stmt (a::lst)) := (stmt_to_string a) ++ "\n" ++ (stmt_to_string (stmt.scope_stmt lst))
| (stmt.scope_stmt []) := "}"
| (stmt.include_stmt l) := "include_stmt: " ++ l
| (stmt.parse_error lst) := "PARSE ERROR: " ++ (lst.take 10).to_string

instance : has_to_string stmt := ⟨stmt_to_string⟩

def consume_until (s : string) : list string → (list string) × (list string) :=
prod.map id tail ∘ span (≠ s)

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
    | ("${" :: l) := let (x, rest) := consume_until "$}" l in
        (stmt.scope_stmt ((parser_core n) x)) :: (pc rest) 
    -- comments go nowhere
    | ("$(" :: l) := let (x, rest) := consume_until "$)" l in (pc rest)
    | ("$[" :: filename :: "$]" :: rest) := stmt.include_stmt filename :: pc rest
    | [] := []
    | l := [(stmt.parse_error l)]
    end

def parser (s : list string) : list stmt := parser_core (length s) s

def whitespace : char -> bool
| ' ' := true
| '\n' := true
| default := false

def lexer := filter (≠ "") ∘ split whitespace

-- IO crap below this line
open io

def parse_from (directory : string) (file : string) : io stmt :=
do s ← fs.read_file (directory ++ file),
   let p := parser $ lexer s.to_string,
   match p with
   | stmt.include_stmt db_file :: rest :=
     do db ← fs.read_file (directory ++ db_file),
        -- lean harassed about recursion, so this only supports one import.
        return $ stmt.scope_stmt $ parser (lexer db.to_string) ++ rest
   | _ := return $ stmt.scope_stmt p
   end

def main : io unit :=
do let dir := "../",
   let file := "twoplustwo.mm",
   parse_from dir file >>= print_ln -- uses to_string instance

#eval parse_from "/Users/smooth/build/twitchcoq/metamath/miu2.mm/" "miu2.mm" >>= print_ln
