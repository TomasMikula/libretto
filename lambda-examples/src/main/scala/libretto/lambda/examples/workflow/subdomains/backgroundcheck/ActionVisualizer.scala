package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.lang.{**, PortName}
import libretto.lambda.examples.workflow.generic.vis.{Approximates, Color, Visualization, Visualizer, Wire}
import libretto.lambda.examples.workflow.generic.vis.Approximates.lump
import libretto.lambda.util.Exists

given Visualizer[Action, Approximates] with {
  import Visualization.LabeledBox

  private val COLOR = Color.rgb(251, 159, 251)

  extension [A, B](f: Action[A, B])
    override def visualize: Exists[[X] =>> Exists[[Y] =>> (
      X Approximates A,
      Y Approximates B,
      Visualization[X, Y],
    )]] = {
      f match
        case Action.SendAcceptanceRequest =>
          summon[A =:= (EmailAddress ** PortName[CandidateResponse])]
          summon[B =:= Unit]

          val v: (Wire ** Wire) Approximates A =
            lump[EmailAddress] ** lump[PortName[CandidateResponse]]
          val w: Wire Approximates B =
            lump[Unit]

          Exists(Exists((
            v,
            w,
            LabeledBox(v.inDesc, w.inDesc, "SendAcceptanceRequest", Some(COLOR))
          )))

        case Action.NotifyVerificationTeam =>
          summon[A =:= (EmploymentHistory ** PortName[EmploymentVerificationResult])]
          summon[B =:= Unit]

          val v: (Wire ** Wire) Approximates A =
            lump[EmploymentHistory] ** lump[PortName[EmploymentVerificationResult]]
          val w: Wire Approximates B =
            lump[Unit]

          Exists(Exists((
            v,
            w,
            LabeledBox(v.inDesc, w.inDesc, "NotifyVerificationTeam", Some(COLOR))
          )))

        case Action.ReportCandidateDeclined =>
          summon[A =:= EmailAddress]
          summon[B =:= Report]

          val v: Wire Approximates A = lump[EmailAddress]
          val w: Wire Approximates B = lump[Report]

          Exists(Exists((
            v,
            w,
            LabeledBox(v.inDesc, w.inDesc, "ReportCandidateDeclined", Some(COLOR))
          )))

        case Action.CreateReport =>
          summon[A =:= (CriminalRecord ** CivilRecord ** EmploymentVerificationResult)]
          summon[B =:= Report]

          val v: (Wire ** Wire ** Wire) Approximates A =
            lump[CriminalRecord] **
            lump[CivilRecord] **
            lump[EmploymentVerificationResult]
          val w: Wire Approximates B =
            lump[Report]

          Exists(Exists((
            v,
            w,
            LabeledBox(v.inDesc, w.inDesc, "CreateReport", Some(COLOR))
          )))

        case Action.CheckCriminalRecord =>
          summon[A =:= PersonalId]
          summon[B =:= CriminalRecord]

          val v: Wire Approximates A = lump[PersonalId]
          val w: Wire Approximates B = lump[CriminalRecord]

          Exists(Exists((
            v,
            w,
            LabeledBox(v.inDesc, w.inDesc, "CheckCriminalRecord", Some(COLOR))
          )))

        case Action.CheckCivilRecord =>
          summon[A =:= PersonalId]
          summon[B =:= CivilRecord]

          val v: Wire Approximates A = lump[PersonalId]
          val w: Wire Approximates B = lump[CivilRecord]

          Exists(Exists((
            v,
            w,
            LabeledBox(v.inDesc, w.inDesc, "CheckCivilRecord", Some(COLOR))
          )))
    }
}
