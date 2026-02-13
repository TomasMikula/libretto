package kindville

// Defined in separate file, so that the Box macros themselves don't see through the opaque type alias
opaque type Box[Code[⋅⋅[_]] <: AnyKind, As] = Any
