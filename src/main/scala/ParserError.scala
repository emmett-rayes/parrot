package parrot

import scala.util.control.NoStackTrace

/** An error indicating a parsing failure. */
class ParserError(message: => String | Null, cause: Throwable | Null = null) extends Exception(cause)
    with NoStackTrace {

  /** The error message. */
  override def getMessage: String | Null = message
}
