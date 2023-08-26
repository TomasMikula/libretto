package libretto.lambda.examples.workflow.generic.runtime

enum Value[F[_], A]:
  /** Extension point for domain-specific values. */
  case Ext(value: F[A])
