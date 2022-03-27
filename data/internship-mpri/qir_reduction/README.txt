README

I) Description of the project

An implementation of the QIR and some reduction strategies.


II) Build instructions

- Go into the src/ folder
- Use  $ ocamlbuild reduce.native  to compile the sources
- Execute $ ./reduce --help for the list of available options
  e.g. $ ./reduce -heuristic 100 < ../test/ads_view.txt
       $ ./reduce -exhaustive < ../test/dupl_ads.txt