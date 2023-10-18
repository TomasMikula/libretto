package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.examples.workflow.generic.runtime.{WorkflowInProgress => WIP}
import libretto.lambda.examples.workflow.generic.lang.FlowAST
import scala.collection.mutable
import scala.util.Try

private[runtime] class Persistor[Action[_, _], Val[_]] {
  private var nextWorkflowId: Long = 1
  private var nextPromiseId: Long = 1

  private enum Entry[A]:
    case Unlocked(sn: Long, w: WIP[Action, Val, A])
    case Locked(sn: Long, w: WIP[Action, Val, A])

  private val workflows: mutable.Map[WorkflowRef[?], Entry[?]] =
    mutable.Map.empty[WorkflowRef[?], Entry[?]]

  private val promises: mutable.Map[PromiseId[?], PromiseState[Val, ?]] =
    mutable.Map.empty[PromiseId[?], PromiseState[Val, ?]]

  def insert[A, B](
    input: Value[Val, A],
    workflow: FlowAST[Action, A, B],
  ): WorkflowRef[B] =
    this.synchronized {
      val id = nextWorkflowId
      nextWorkflowId += 1
      val ref = WorkflowRef[B](id)
      val wip = WIP.init(input, workflow)
      workflows.put(ref, Entry.Unlocked(0L, wip))
      ref
    }

  def pollWorkItem(): Option[WorkItem] =
    this.synchronized {
      workflows.collectFirst {
        case (ref, Entry.Unlocked(_, wf)) if wf.isReducible => WorkItem.Wakeup(ref)
      }
    }

  def modifyOpt[A](ref: WorkflowRef[A])(
    f: WIP[Action, Val, A] => Option[WIP[Action, Val, A]],
  ): ModifyRes =
    lockAndGet(ref) match
      case LockGetRes.Acquired(token, w) =>
        f(w) match
          case Some(w1) =>
            setAndUnlock(ref, token, w1) match
              case UnlockRes.Success => ModifyRes.Modified
              case UnlockRes.NotFound => ModifyRes.NotFound
              case UnlockRes.LockExpired => ModifyRes.InUse
          case None =>
            unlock(ref, token) match
              case UnlockRes.Success => ModifyRes.NoChange
              case UnlockRes.NotFound => ModifyRes.NotFound
              case UnlockRes.LockExpired => ModifyRes.InUse
      case LockGetRes.NotFound() =>
        ModifyRes.NotFound
      case LockGetRes.InUse() =>
        ModifyRes.InUse

  enum ModifyRes:
    case NotFound
    case InUse
    case NoChange
    case Modified

  private def lockAndGet[A](ref: WorkflowRef[A]): LockGetRes[A] =
    this.synchronized {
      workflows.get(ref) match {
        case Some(entry) =>
          entry match
            case Entry.Unlocked(n, w) =>
              workflows.put(ref, Entry.Locked(n, w))
              LockGetRes.Acquired(n, w).asInstanceOf[LockGetRes[A]]
            case Entry.Locked(_, _) =>
              LockGetRes.InUse()
        case None =>
          LockGetRes.NotFound()
      }
    }

  private def setAndUnlock[A](ref: WorkflowRef[A], token: Long, w: WIP[Action, Val, A]): UnlockRes =
    this.synchronized {
      workflows.get(ref) match {
        case Some(entry) =>
          entry match
            case Entry.Locked(n, _) =>
              if (n > token)
                UnlockRes.LockExpired
              else
                workflows.put(ref, Entry.Unlocked(n+1, w))
                UnlockRes.Success
            case Entry.Unlocked(_, _) =>
              UnlockRes.LockExpired
        case None =>
          UnlockRes.NotFound
      }
    }

  private def unlock[A](ref: WorkflowRef[A], token: Long): UnlockRes =
    this.synchronized {
      workflows.get(ref) match {
        case Some(entry) =>
          entry match
            case Entry.Locked(n, w) =>
              if (n > token)
                UnlockRes.LockExpired
              else
                workflows.put(ref, Entry.Unlocked(n+1, w))
                UnlockRes.Success
            case Entry.Unlocked(_, _) =>
              UnlockRes.LockExpired
        case None =>
          UnlockRes.NotFound
      }
    }

  def pollResult[A](ref: WorkflowRef[A]): Option[WorkflowResult[Val, A]] =
    this.synchronized {
      workflows
        .get(ref)
        .flatMap {
          case Entry.Unlocked(_, w) =>
            w.resultOpt
              .map(_.asInstanceOf[WorkflowResult[Val, A]])
          case Entry.Locked(_, _) =>
            None
        }
    }

  def promise[A](w: WorkflowRef[?]): PromiseId[A] =
    this.synchronized {
      val id = PromiseId[A](w, nextPromiseId)
      nextPromiseId += 1
      promises.put(id, PromiseState.Empty())
      id
    }

  def completePromise[A](id: PromiseId[A], result: Try[Value[Val, A]]): Boolean =
    this.synchronized {
      promises.get(id) match
        case None =>
          false
        case Some(value) =>
          value match
            case PromiseState.Empty() =>
              promises.put(id, PromiseState.Complete(result))
              true
            case PromiseState.Complete(_) =>
              false
    }

  def fetchResult[A](id: PromiseId[A]): Option[Try[Value[Val, A]]] =
    this.synchronized {
      promises.get(id).flatMap {
        case PromiseState.Complete(result) =>
          Some((result: Try[Value[Val, ?]]).asInstanceOf[Try[Value[Val, A]]])
        case PromiseState.Empty() =>
          None
      }
    }

  enum LockGetRes[A]:
    case Acquired(token: Long, w: WIP[Action, Val, A])
    case NotFound()
    case InUse()

  enum UnlockRes:
    case Success
    case NotFound
    case LockExpired
}
