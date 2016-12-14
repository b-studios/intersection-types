# Intersection Types implemented by HLists
This small library implements an embedding of user defined intersection
types by encoding them as HLists. The approach is similar to Dunfield's
elaboration to LC with tuples.

To use this library either immediately require it as [github repository](http://stackoverflow.com/questions/7550376/how-can-sbt-pull-dependency-artifacts-from-git)
in your project or clone the repository and run `sbt publishLocal`.
Afterwards you should be able to use it as a dependency via:

```scala
libraryDependencies += "de.bstudios" %% "intersection" % "0.1-SNAPSHOT"
```