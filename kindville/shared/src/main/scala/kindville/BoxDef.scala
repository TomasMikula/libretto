package kindville

// Defined in separate file, because otherwise macros expand the alias despite being opaque.
// https://github.com/scala/scala3/issues/13461
opaque type Box[As, Code[⋅⋅[_]] <: AnyKind] = Any
