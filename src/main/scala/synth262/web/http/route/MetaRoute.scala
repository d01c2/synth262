package synth262.web.http.route

import synth262.web.*
import synth262.web.http.*
import cats.effect.*
import io.circe.*, io.circe.syntax.*, io.circe.parser.*
import org.http4s.dsl.io.*
import org.http4s.{HttpApp, HttpRoutes}

object MetaRoute {
  def apply() = HttpRoutes.of[IO] {
    case GET -> Root / "version" =>
      synth262.VERSION.asJsonOk
  }
}
