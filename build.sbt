name := "intersection"

organization := "de.bstudios"

version := "0.1-SNAPSHOT"

scalaVersion := "2.12.1"

crossScalaVersions := Seq("2.10.6", "2.11.2", "2.11.8", "2.12.1")

libraryDependencies += "com.chuusai" %% "shapeless" % "2.3.2"

// css patches to Scala Doc
doc in Compile := {
  val x = (doc in Compile).value
  val libFolder = (target in Compile).value / s"scala-${(scalaBinaryVersion in Compile).value}" / "api" / "lib"

  val cssPatch =
    """|.cmt h4 { font-size: 1.5em }
       |.cmt code {
       |    font-weight: normal !important;
       |    padding: 0 0.5em;
       |    border: 0px solid #ddd;
       |    background-color: #fff;
       |    font-family: "Source Code Pro", "Monaco", "Ubuntu Mono Regular", "Lucida Console", monospace;
       |}
    """.stripMargin

  IO.write(libFolder / "index.css", cssPatch, append = true)
  x
}