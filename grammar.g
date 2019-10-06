start : inductive
      | assertion


// ident
first_letter : ("a".."z") | ("A".."Z") | "_"
subsequent_letter : ("a".."z") | ("A".."Z") | ("0".."9") | "'" | "_"
ident : first_letter subsequent_letter*
name : ident | "_"

// term
sort : "Prop" | "Set" | "Type"
term : "forall" binders "," term
     | term "->" term
     | sort
     | ident // questionable here

// binder (is wrong)
binder : name [":" term]
binders : binder+

ind_body : ident [binders] ":" term ":=" ("|" ident [binders])+
inductive : "Inductive" ind_body "."

assertion : assertion_keyword ident [binders] ":" term "."
assertion_keyword : "Theorem" | "Lemma"

%ignore " "
%ignore "\n"

COMMENT : "(**" /(.|\n|\r)+/ "**)"
%ignore COMMENT

