package libretto.mashup.dsl

sealed trait AbstractRecord

case class Record() extends AbstractRecord

class ##[Init <: AbstractRecord, Last <: Field] extends AbstractRecord

sealed trait Field
class of[Name <: String, T] extends Field
