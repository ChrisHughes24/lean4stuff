import Lake
open Lake DSL

package «Stuff»

lean_lib Stuff


@[defaultTarget]
lean_exe «stuf» {
  root := `Stuff
  supportInterpreter := true
}


