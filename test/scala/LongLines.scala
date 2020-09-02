import java.util.regex.Pattern

object LongLines {
  /**
   *
   * @param line Line to be processed.
   * @param width Max width of any given line. Will try to wrap to half if poss.
   * @param indent Indent of wrapped lines (not the first line).
   * @return Hard wrapped line.
   */
    def processLine(line: String, width: Int = 80,
                    indent: Int = 4): String = {
      if (line.length() > width) {
        val pattern = Pattern.compile("[^-a-zA-Z0-9.\\s/\")]")
        val matcher = pattern.matcher(line)
        if(matcher.find(width/2)){
          val padding = " " * indent
          val separation = matcher.start() + 1
          line.substring(0, separation) + "\n" +
          padding + processLine(line.substring(separation).trim)
        } else line.substring(0, width-1) + "\n" +
               processLine(line.substring(width-1))
      }
      else line
    }
}