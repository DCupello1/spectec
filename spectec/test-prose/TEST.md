# Preview

```sh
$ (cd ../spec && dune exec ../src/exe-watsup/main.exe -- *.watsup -v -l --sideconditions --animate --prose)
watsup 0.3 generator
== Parsing...
== Elaboration...
== IL Validation...
== Running pass sideconditions
== IL Validation...
== Running pass animate
Animation failed.
Valtype_sub: `|-%<:%`(t, t')
if ((t' = (numtype <: valtype)) \/ (t' = (vectype <: valtype)))
...Animation failed
Animation failed.
(if (l < |C.LABEL_context|))*{l}
if (l' < |C.LABEL_context|)
(Resulttype_sub: `|-%*<:%*`(t*{t}, C.LABEL_context[l]))*{l}
Resulttype_sub: `|-%*<:%*`(t*{t}, C.LABEL_context[l'])
...Animation failed
Animation failed.
if (0 < |C.MEM_context|)
if ((n?{n} = ?()) <=> (sx?{sx} = ?()))
if (C.MEM_context[0] = mt)
if ((2 ^ n_A) <= ($size(nt <: valtype) / 8))
(if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(nt <: valtype) / 8))))?{n}
if ((n?{n} = ?()) \/ (nt = (in <: numtype)))
...Animation failed
Animation failed.
if (0 < |C.MEM_context|)
if (C.MEM_context[0] = mt)
if ((2 ^ n_A) <= ($size(nt <: valtype) / 8))
(if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(nt <: valtype) / 8))))?{n}
if ((n?{n} = ?()) \/ (nt = (in <: numtype)))
...Animation failed
Animation failed.
if ($vvunop(vvunop, vt, cv_1) = cv)
...Animation failed
== IL Validation...
== Translating to AL...
/home/suhyeon/spectec/spectec/_build/default/spec/../src/exe-watsup/main.exe: uncaught exception Not_found
Raised at Stdlib__List.find in file "list.ml", line 232, characters 10-25
Called from Backend_interpreter__Translate.split_context_winstr in file "src/backend-interpreter/translate.ml", line 704, characters 21-43
Called from Backend_interpreter__Translate.reduction_group2algo in file "src/backend-interpreter/translate.ml", line 743, characters 24-65
Called from Stdlib__List.map in file "list.ml", line 86, characters 15-19
Called from Stdlib__List.map in file "list.ml", line 88, characters 14-21
Called from Backend_interpreter__Translate.translate in file "src/backend-interpreter/translate.ml", line 928, characters 37-55
Called from Dune__exe__Main in file "src/exe-watsup/main.ml", line 180, characters 8-50
[2]
```
