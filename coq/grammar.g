start : sentence+

sentence : inductive
         | assertion
         | definition
         | stupid

stupid : "Declare" /(.)+/
       | "Set" /(.)+/
       | "Reserved" /(.)+/
       | "Notation" /(.)+/
       | "Print" /(.)+/

// ident
FIRST_LETTER : ("a".."z") | ("A".."Z") | "_"
SUBSEQUENT_LETTER : ("a".."z") | ("A".."Z") | ("0".."9") | "'" | "_"
IDENT : FIRST_LETTER SUBSEQUENT_LETTER*
access_ident : "." IDENT
name : IDENT | "_"

// term
qualid : IDENT | qualid access_ident
arg : term
    | "(" IDENT ":=" term ")"
sort : "Prop" | "Set" | "Type"

match_item : term ["as" name] ["in" qualid [pattern]*]
return_type : "return" term

pattern : qualid
mult_pattern : pattern  // broken
equation : mult_pattern "=>" term

// "exists" and "=" are not a part of the language
term : "forall" binders "," term
     | "match" match_item [return_type] "with" ["|" equation ["|" equation]* ] "end"
     | "if" term "then" term "else" term
     | "(" term ")"
     | term "->" term  // fake, this notation is defined
     | term arg+ // function call
     | sort
     | qualid

// this is really wrong
tactic : "exact" term "."

proof : "Proof." tactic* ("Qed." | "Abort.")

// binder (is wrong but closer)
binder : name
       | name+ [":" term]
       | "(" name+ [":" term] ")"
       | "(" name [":" term] ":=" term ")"
binders : binder+

ind_body : IDENT [binders] ":" term ":=" [["|"] IDENT [binders] [":" term]] ("|" IDENT [binders] [":" term])*
inductive : "Inductive" ind_body "."

definition : "Definition" IDENT [binders] [":" term] ":=" term "."

// TODO: does proof belong here?
assertion : assertion_keyword IDENT [binders] ":" term "." proof
assertion_keyword : "Theorem" | "Lemma"

%ignore " "
%ignore "\n"

COMMENT : "(*" /(.|\n)+?/ "*)"
%ignore COMMENT

