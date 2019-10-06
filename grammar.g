start : sentence+

sentence : inductive
         | assertion
         | proof
         | definition

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
sort : "Prop" | "Set" | "Type"  // are this all the same thing?

// "exists" and "=" are not a part of the language
term : "forall" binders "," term
     | term "->" term
     | term arg+
     | "if" term "then" term "else" term
     | sort
     | qualid
     | "(" term ")"

// this is really wrong
tactic : name term "."
       | name "."
       | name term ";" tactic
       | name ";" tactic

proof : "Proof." tactic* ("Qed." | "Abort.")

// binder (is wrong but closer)
binder : name
       | name+ [":" term]
       | "(" name+ [":" term] ")"
       | "(" name [":" term] ":=" term ")"
binders : binder+

ind_body : IDENT [binders] ":" term ":=" (["|"] IDENT [binders] ":" term) ("|" IDENT [binders] ":" term)*
inductive : "Inductive" ind_body "."

definition : "Definition" IDENT [binders] [":" term] ":=" term "."

assertion : assertion_keyword IDENT [binders] ":" term "."
assertion_keyword : "Theorem" | "Lemma"

%ignore " "
%ignore "\n"

COMMENT : "(**" /(.|\n|\r)+/ "*)"
%ignore COMMENT

