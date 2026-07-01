package synth262.state

import synth262.cfg.*

/** provenance of addresses */
case class Provenance(
  cursor: Cursor,
  feature: Option[Feature],
) extends StateElem
