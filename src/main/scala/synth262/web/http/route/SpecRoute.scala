package synth262.web.http.route

import synth262.cfg.CFG
import synth262.spec.util.JsonProtocol.given
import synth262.web.*
import synth262.web.http.*
import synth262.web.util.JsonProtocol
import cats.effect.*
import io.circe.*, io.circe.syntax.*, io.circe.parser.*
import org.http4s.HttpRoutes
import org.http4s.dsl.io.*

object SpecRoute {
  def apply(cfg: CFG) = HttpRoutes.of[IO] {
    case GET -> Root / "func" =>
      cfg.asJsonOk(using JsonProtocol(cfg).cfgToFuncEncoder)
    case GET -> Root / "version" =>
      cfg.spec.version.asJsonOk
  }
}
