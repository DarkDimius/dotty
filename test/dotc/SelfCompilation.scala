package dotc

import test._
import java.io.{FilenameFilter, File}

object SelfCompilation {
  val dotcDir = "src/dotty/"

  val dotcSources: List[String] = allScalaFiles(dotcDir)

  def allScalaFiles(dir: String): List[String] = allScalaFiles(new File(dir))
  def allScalaFiles(dir: File): List[String] = {
    val files = dir.listFiles()
    val result = collection.mutable.ListBuffer[String]()
    for (file <- files) {
      if (file.isDirectory) {
        result ++= allScalaFiles(file)
      }
      else if (file.getName.endsWith(".scala")) {
        result += file.getAbsolutePath
      }

    }
    result.toList
  }

  def main(args:Array[String]) = {
    val args = dotcSources.toArray
    for(i<- 1 to 1000)
      new CompilerRun().run(args)
  }
}


class CompilerRun extends CompilerTest {
  def run(arguments: Array[String]) =      compileArgs(arguments.toArray)
}