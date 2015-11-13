(***********************************************************
   Use a command such as 
      isabelle build -D .
   to produce the pdf document for these theories.
***********************************************************)

session "b-means" = "HOL" +
  description
    "Semantics of the behavior of software components developed with the B method"
  options
    [ quick_and_dirty=false, 
      browser_info,
      document = pdf, 
      document_output = "output", 
      document_variants="document:outline=/proof,/theory" ]
(*  theories [document = false] *)
  theories
    LTSb Simulationb Bmethodb Compositionb
  document_files
    "root.tex"
