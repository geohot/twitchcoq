import system.io
import init.data.string.ops

def double_str : string -> string
| s := s ++ s

def whitespace : char -> bool
| ' ' := true
| '\n' := true
| default := false

-- IO crap below this line
open io

def get_file : io char_buffer :=
    fs.read_file "/Users/smooth/build/twitchcoq/metamath/simple.mm"

def main : io unit :=
do a <- get_file,
   let b := a.to_string.split whitespace,
   put_str (string.join b)

#eval main
