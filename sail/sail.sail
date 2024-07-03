default Order dec

$include <prelude.sail>

val zero_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function zero_extend(m, v) = sail_zero_extend(v, m)

register SOME_REG    : bits(32) = 0x00000401
register ANOTHER_REG : bits(16) = 0x1234

val addition : bits(32) -> bits(32)
function addition(value) = {
  value + 57
}
val reading: unit -> bits(32)
function reading() = {
  SOME_REG
}

val combining: unit -> unit
function combining() = {
  SOME_REG = addition(reading())
}

val writing: bits(32) -> unit
function writing(value) = {
  SOME_REG = value
}
