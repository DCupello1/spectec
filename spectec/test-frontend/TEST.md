# Preview

```sh
$ (cd ../spec && dune exec ../src/exe-watsup/main.exe -- *.watsup -v -l --print-il --check)
Error: A running dune (pid: 31781) instance has locked the build directory.
If this is not the case, please delete _build/.lock
[1]
```
