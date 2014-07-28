(***********************************************************
   Use a command such as 
      isabelle build -D .
   to produce the pdf document for these theories.
***********************************************************)

session "b-means" = "HOL" +
  options [ (*quick_and_dirty = true,*) document = pdf, document_output = "output", document_variants="document:outline=/proof,/theory" ]
(*  theories [document = false] *)
  theories
    LTS Simulation TraceRefinement
  files "document/root.tex"
