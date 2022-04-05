#![deny(rust_2018_idioms)]
#![allow(dead_code)]
//! ## Unrecurse
//! **This is in prototype state** As far as author knows the general idea is sound and even passes miri.
//! but there are still a lot of rough edges internally and in public api.
//!
//! Helper to convert recursive approach into iterative.
//!
//! This crate consists from following main parts.
//!  - [`RefStack`] struct for direct and granular access to stack. But only supports references for now.
//!  - [`run`] to be able to store a struct that references previous element on stack.
//!  - [`run_async`]  to rewrite async recursion without recursion/macros/allocating every future
//!  - [`run_async_backref`] if you have async recursion where current stack frame contains references to previous one
//!
//!
//! The most simple method to use is `run_async(_backref)`.
//! You can just convert your current recursive function into async fn. Add `RecursionRef` parameter.
//! Use it to invoke recursion and voila. It still looks like a recursion so it is still easy to reason about it
//! but internally it uses async machinery to execute everything sequentially using a dedicated stack for current state.
//! But currently quite often futures in rust are not very optimized. So if generated future is too big you might want to
//! resort to the `run` function which allows you to create your own state to store in internal stack.
//!

// todo better examples

// use futures::AsyncReadExt;
use std::future::Future;
use std::marker::PhantomData;
use std::mem::{transmute_copy, ManuallyDrop, MaybeUninit};
use std::ops::{Deref, DerefMut};
use std::pin::Pin;
use std::ptr::NonNull;
use std::task::Poll;

/// With this struct you can save full state of current iteration including references
/// so that when you pop that state back you now have full context available
/// as if you just returned from the function call.
/// Basically you just push current state into `RefStack`
/// and then pop back when you need to return to that state.
/// Exactly what compiler does with regular call stack when you do recursive call.
/// And what `RefStack` does is sound precisely for that reason,
/// it just emulates what compiler already does just in a dedicated structure.
pub struct RefStack<'a, T, Metadata = ()> {
    // SAFETY:
    // this is basically a borrow stack in Stacked Borrows sense, so as long as we create
    // references only from the last pointer, every pointer is derived from previous one
    // and there are no active references when we pop then everything is sound.
    // Also that's basically what compiler already does with regular function calls.
    // Essentially when we call a function all references on previous stack
    // frame become inactive(pretty much like raw pointers we use here)
    // and you have only access to function arguments(last element here)
    stack: Vec<*mut T>,
    metadata: Vec<Metadata>,
    phantom: PhantomData<&'a mut T>,
}

impl<'a, T, M: Default> RefStack<'a, T, M> {
    pub fn new(init: &'a mut T) -> Self {
        Self {
            stack: vec![init],
            metadata: vec![M::default()],
            phantom: PhantomData,
        }
    }

    /// Pushes new state that was created from previous one with closure.
    pub fn push_with(&mut self, f: impl FnOnce(&mut T) -> &mut T) {
        // let curr = self.current.take().unwrap();
        // self.stack.push(curr as _);
        let next = f(self.current()) as *mut _;
        self.stack.push(next);
        self.metadata.push(M::default())
    }

    /// Pops state from stack
    pub fn pop(&mut self) -> Option<&mut T> {
        self.metadata.pop();
        // SAFETY: we operate on `&mut self`
        // so there are no active references into stack at that point
        // see also struct declaration
        self.stack.pop().map(|x| unsafe { &mut *x })
    }

    /// Current reference in the end of a stack
    pub fn current(&mut self) -> &mut T {
        // SAFETY:
        // we can get access only to the last element so it is fine
        // see also struct declaration
        unsafe { &mut *self.stack.last().copied().unwrap() }
    }

    /// Gets additional metadata for current state
    pub fn meta(&mut self) -> &mut M {
        self.metadata.last_mut().unwrap()
    }

    /// Current stack size
    pub fn len(&self) -> usize {
        self.stack.len()
    }
}

// todo
// pub struct GenericRefStack<'a, T: 'a, const CHUNK_SIZE: usize = 30> {
//     stack: ChainArena<MaybeUninit<T>, CHUNK_SIZE>,
//     phantom: PhantomData<&'a mut T>,
//     pin: PhantomPinned,
// }
//
// impl<'a, T, const CHUNK_SIZE: usize> GenericRefStack<'a, T, CHUNK_SIZE> {
//     pub fn new(init: T) -> Self {
//         let mut stack = ChainArena::new();
//         stack.push(MaybeUninit::new(init));
//         Self {
//             stack,
//             phantom: PhantomData,
//             pin: PhantomPinned,
//         }
//     }
//
//     // pub fn push_with<F>(self:Pin<&mut Self>, f: F)
//     // where
//     //     F: for<'x> MyFnOnce<&'x mut T>,
//     //     F: FnOnce(&'a mut T) -> T + 'static,
//     // {
//     //     let this = unsafe { self.get_unchecked_mut() };
//     //     // let curr = self.current.take().unwrap();
//     //     // self.stack.push(curr as _);
//     //     let next = f(this.current_inner());
//     //     this.stack.push(MaybeUninit::new(next));
//     // }
//     pub fn loop_with<F>(&mut self, f: F)
//     where
//         T: for<'x> WithLifetime<'x, 'a>,
//         F: for<'x> FnMut(
//             &'x mut <T as WithLifetime<'x, 'a>>::Applied,
//         ) -> Option<<T as WithLifetime<'x, 'a>>::Applied>,
//         F: FnMut(&'a mut T) -> Option<T>,
//     {
//         loop {
//             let curr = self.current_inner();
//             unsafe {
//                 match f(curr) {
//                     /* ControlFlow::Break(r) => return Some(r), */
//                     None => self.pop_inner()?,
//                     Some(n) => self.stack.push(MaybeUninit::new(n)),
//                 }
//             }
//         }
//     }
//
//     pub fn advance<'b, F, Y>(&'b mut self, f: F) -> Option<Y>
//     where
//         T: for<'x> WithLifetime<'x, 'a>,
//         Y: for<'x> WithLifetime<'x, 'b>,
//         F: for<'x, 'y> FnOnce(
//             &'x mut <T as WithLifetime<'y, 'a>>::Applied,
//         ) -> Action<
//             <Y as WithLifetime<'x, 'b>>::Applied,
//             <T as WithLifetime<'x, 'a>>::Applied,
//         >,
//         // F: FnOnce(&'a mut T) -> Action<R, T>,
//     {
//         // loop {
//         if self.is_empty() {
//             return None;
//         }
//         let curr = self.current_inner();
//         match f(curr) {
//             Action::Yield(r) => return Some(r),
//             Action::Return(()) => self.pop_inner(),
//             Action::Recurse(n) => self.stack.push(MaybeUninit::new(n)),
//         }
//         // }
//     }
//
//     pub fn advance_deref<'b, F, Y>(&'b mut self, f: F) -> Option<Y>
//     where
//         T: for<'x> WithLifetime<'x, 'a> + StableDeref,
//         Y: for<'x> WithLifetime<'x, 'b>,
//         F: for<'x, 'y> FnOnce(
//             &'x mut T::Target,
//         ) -> Action<
//             <Y as WithLifetime<'x, 'b>>::Applied,
//             <T as WithLifetime<'x, 'a>>::Applied,
//         >,
//         // F: FnOnce(&'a mut T) -> Action<R, T>,
//     {
//         // loop {
//         if self.is_empty() {
//             return None;
//         }
//         let curr = self.current_inner();
//         match f(curr) {
//             Action::Yield(r) => return Some(r),
//             Action::Return(()) => self.pop_inner(),
//             Action::Recurse(n) => self.stack.push(MaybeUninit::new(n)),
//         }
//         // }
//     }
//
//     pub fn pop_inner(&mut self) -> Option<T> {
//         unsafe { self.stack.pop().map(|x| x.assume_init()) }
//     }
//
//     pub fn push_with<F>(mut self: &mut Pin<&mut Self>, f: F)
//     where
//         T: for<'x> WithLifetime<'x, 'a>,
//         F: for<'x, 'y> FnOnce(
//             &'x mut <T as WithLifetime<'y, 'a>>::Applied,
//         ) -> <T as WithLifetime<'x, 'a>>::Applied,
//         F: FnOnce(&'a mut T) -> T,
//     {
//         // let curr = self.current.take().unwrap();
//         // self.stack.push(curr as _);
//         let next = f(self.as_mut().inner().current_inner());
//         self.as_mut().inner().stack.push(MaybeUninit::new(next));
//     }
//
//     fn inner(self: Pin<&mut Self>) -> &mut Self {
//         unsafe { self.get_unchecked_mut() }
//     }
//
//     pub fn pop(self: Pin<&mut Self>) -> Option<T> {
//         self.inner().stack.pop().map(|x| unsafe { x.assume_init() })
//         // self.inner().stack.pop().map(|_| ())
//     }
//
//     fn current_inner(&mut self) -> &'a mut T {
//         unsafe { &mut *(self.stack.last_mut().unwrap().assume_init_mut() as *mut _) }
//     }
//
//     pub fn current(self: Pin<&mut Self>) -> &mut T {
//         self.inner().current_inner()
//     }
//
//     pub fn is_empty(&self) -> bool {
//         self.stack.is_empty()
//     }
// }
/// Used to rewrite post order processing of recursive data structures in iterative way.
/// Struct that you want to use as a current state must implement [`WithLifetime`] properly.
pub fn run<T, F, R: Default>(init: T, mut f: F) -> R
where
    T: for<'x> WithLifetime<'x>,
    F: for<'x, 'y> FnMut(
        &'x mut <T as WithLifetime<'y>>::Applied,
    ) -> Action<<T as WithLifetime<'x>>::Applied, R>,
    // T: for<'x> ShrinkLifetime<'x>,
    // F: for<'x, 'y> FnMut(
    //     &'x mut <T as ShrinkLifetime<'y>>::BoundApplied,
    // ) -> Action<<T as ShrinkLifetime<'x>>::BoundApplied, R>,
{
    //     run2::<_, _, _, ()>(init, f)
    // }
    //
    // pub fn run2<'a, T, F, R: Default, Marker>(init: T, mut f: F) -> R
    // where
    //     T: for<'x> WithLifetime<'x, 'a, Marker>,
    //     // for<'x> <T as WithLifetime<'x, 'a, Marker>>::Applied: Sized,
    //     F: for<'x, 'y> FnMut(
    //         &'x mut <T as WithLifetime<'y, 'a, Marker>>::Applied,
    //     ) -> Action<<T as WithLifetime<'x, 'a, Marker>>::Applied, R>,
    //     // F: FnMut(&'a mut T) -> Option<T>,
    // {
    let mut stack = ChainArena::<_, 30>::new();
    stack.push(init);
    loop {
        let curr = if let Some(x) = stack.last_mut() {
            x
        } else {
            return R::default();
        };
        unsafe {
            match f(core::mem::transmute(curr)) {
                /* ControlFlow::Break(r) => return Some(r), */
                Action::Return(()) => {
                    stack.pop();
                }
                Action::Yield(r) => return r,
                Action::Recurse(n) => stack.push(WithLifetime::move_with_lifetime_back(n)),
            }
        }
    }
}

// pub struct Wrap<'x, T>(MaybeUninit<T>, PhantomData<fn(&'x T) -> &'x ()>);
// impl<'x, T> Drop for Wrap<'x, T> {
//     fn drop(&mut self) {
//         unsafe { core::ptr::drop_in_place(self.0.as_mut_ptr()) }
//     }
// }
// impl<'x, T> Wrap<'x, T>
// where
//     T: WithLifetime<'x>,
// {
//     fn from(f: T) -> Self {
//         // Wrap(MaybeUninit::new(f), PhantomData)
//         Wrap(f, PhantomData)
//     }
//
//     pub fn into_inner(self) -> T::Applied {
//         unsafe { self.0.assume_init().move_with_lifetime() }
//         // unsafe { self.0.as_ptr().read().move_with_lifetime() }
//     }
// }
//
// impl<'x, T> Deref for Wrap<'x, T>
// where
//     T: WithLifetime<'x>,
// {
//     type Target = T::Applied;
//
//     fn deref(&self) -> &Self::Target {
//         // unsafe { self.0.assume_init_ref().with_lifetime() }
//         unsafe { self.0.assume_init_read().with_lifetime() }
//     }
// }
// impl<'x, T> DerefMut for Wrap<'x, T>
// where
//     T: WithLifetime<'x>,
// {
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         // unsafe { self.0.assume_init_mut().with_lifetime_mut() }
//         unsafe { self.0.assume_init_mut().with_lifetime_mut() }
//     }
// }

/// Shorthand for `futures::executor::block_on(run_async())`
/// if you want to rewrite regular recursion using async one
pub fn run_async_blocking<F, T, R>(init: T, f: F) -> R
where
    F: for<'x> AsyncFnMut2<T, Recursion<'x, T, R>, Output = R>,
{
    futures_executor::block_on(run_async(init, f))
}

// /// Shorthand for `futures::executor::block_on(run_async_checked())`
// /// if you want to rewrite regular recursion using async one
// pub fn run_async_blocking_checked<F, Fut, T, R>(init: T, mut f: F) -> R
// where
//     F: FnMut(T, RecursionChecked<T, R>) -> Fut,
//     Fut: Future<Output = Checked<R>>,
// {
//     futures_executor::block_on(run_async_checked(init, f))
// }

//  unsound, it is possible to move `RecursionChecked` into spawned task
// and then current future can be cancelled so `RecursionChecked` now contains dangling references
// async fn run_async_checked<F, Fut, T, R>(init: T, mut f: F) -> R
//     where
//         F: FnMut(T, RecursionChecked<T, R>) -> Fut,
//         Fut: Future<Output = Checked<R>>,
// {}

/// More capable version of [`run_async`].
pub async fn run_async_with_data<F, T, R, D>(init: T, data: &mut D, mut f: F) -> R
where
    F: for<'x> AsyncFnMut3<T, Data<'x, D>, Recursion<'x, T, R>, Output = R>,
{
    // todo rewrite using run_async_backref_with_data when Withlifetime will support marker
    // it is possible to use qcell::LCell and no unsafe but it would require adding
    // second lifetime to `Recursion` which might be confusing to users
    // qcell::LCellOwner::scope(|owner| {
    let mut result = None;
    let mut next = None;

    let data = Data(AliasableMut::from(data));
    let mut ret = RecursionChecked::new(&mut next, &mut result);
    let mut ret = AliasableMut::from(&mut ret);
    let mut stack = ChainArena::<_, 30>::new();
    let arg = init;

    // let mut ret = RecursionChecked(
    //     unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(None)).into()) },
    //     unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(None)).into()) },
    // );
    unsafe {
        stack.push(f.call(arg, data.copy(), core::ptr::read(&ret)));
    }
    loop {
        // SAFETY: ChainArena does not move elements even when pushed into so it is safe to Pin the element
        let poll = futures_util::poll!(unsafe { Pin::new_unchecked(stack.last_mut().unwrap()) });
        if let Poll::Ready(returned) = poll {
            stack.pop();
            if stack.is_empty() {
                return returned;
            }
            unsafe {
                core::ptr::write(ret.1.as_ptr(), Some(returned));
            }
        } else {
            let next = unsafe { ret.0.as_mut().take() };
            if let Some(arg) = next {
                // let ret = Recursion(&next, &result);
                // let arg = unsafe { core::mem::transmute_copy(&arg) };
                unsafe {
                    stack.push(f.call(arg, data.copy(), core::ptr::read(&ret)));
                }
            } else {
                // not our return so forward waiting
                futures_util::pending!();
            }
        }
    }
    // })
}

/// Function to invoke async recursion without `Box`ing every future.
/// Often you can already rewrite your async recursion with `futures::stream::unfold`.
/// But it has some limitations,
/// `run_async` on the other hand has exactly same capabilities as a regular async recursion.
/// You can also use it as a simpler version of [`run`].
///
/// Internally it allocates initial 30-elements buffer(number will be customizable in the next versions) of futures on stack.
/// And then if recursion is deeper than that it will allocate linked list of such buffers to allow deep recursion.
///
/// #### Warning
/// Due to bugs in compiler currently it only supports `F` to be an `async fn`.
/// Nevertheless there is still possibility to access additional data with [`run_async_with_data`].
pub async fn run_async<'a, F, T, R>(init: T, mut f: F) -> R
where
    F: for<'x> AsyncFnMut2<T, Recursion<'x, T, R>, Output = R>,
{
    async fn delegator<T, F, R>(arg: T, mut f: Data<'_, F>, rec: Recursion<'_, T, R>) -> R
    where
        F: for<'x> AsyncFnMut2<T, Recursion<'x, T, R>, Output = R>,
    {
        f.access_with(|f: &mut _| f.call(arg, rec)).await
    }
    run_async_with_data(init, &mut f, delegator).await
}

struct SendSyncPtr<T>(*mut T);
impl<T> Clone for SendSyncPtr<T> {
    fn clone(&self) -> Self {
        SendSyncPtr(self.0)
    }
}
impl<T> Copy for SendSyncPtr<T> {}
unsafe impl<T: Send> Send for SendSyncPtr<T> {}
unsafe impl<T: Sync> Sync for SendSyncPtr<T> {}

/// Same as [`run_async`] but allows to run recursion where current state/future has references into previous one.
///
/// #### Warning
/// Due to bugs in compiler currently it only supports `F` to be an `async fn`.
/// Nevertheless there is still possibility to access additional data with [`run_async_backref_with_data`].
// `R` can also be `WithLifetime` here, but i could not find any realistic use-cases where it is necessary,
// so it would just require user to implement `WithLifetime` for `R` for no reason
pub async fn run_async_backref<F, T, R>(init: T, mut f: F) -> R
where
    T: for<'x> WithLifetime<'x>,
    F: for<'x> AsyncFnMut2<
        <T as WithLifetime<'x>>::Applied,
        RecursionContext<'x, T, R>,
        Output = R,
    >,
{
    fn delegator<'a, T, F, R>(
        arg: <T as WithLifetime<'a>>::Applied,
        mut f: Data<'a, F>,
        rec: RecursionContext<'a, T, R>,
    ) -> impl Future<Output = R> + 'a
    where
        T: for<'x> WithLifetime<'x>,
        F: for<'x> AsyncFnMut2<
            <T as WithLifetime<'x>>::Applied,
            RecursionContext<'x, T, R>,
            Output = R,
        >,
    {
        f.access_with(|f: &mut _| f.call(arg, rec))
    }
    run_async_backref_with_data(init, &mut f, delegator).await
}

/// Workaround for a compiler bug
pub struct ForceFutureSend<SendMarkers, Fut>(Fut, PhantomData<SendMarkers>);
unsafe impl<M: Send, F> Send for ForceFutureSend<M, F> {}
impl<M, F: Future> Future for ForceFutureSend<M, F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        //SAFETY: just a simple delegation
        unsafe { Pin::new_unchecked(&mut self.get_unchecked_mut().0) }.poll(cx)
    }
}

struct SendWrapper<T, Marker>(T, PhantomData<Marker>);
unsafe impl<T, Marker: Send> Send for SendWrapper<T, Marker> {}

/// Version of [`run_async_backref`] that supports additional data to pass into
pub fn run_async_backref_with_data<'b, 'a: 'b, T: 'a, F: 'a, R: 'a, D: 'a>(
    init: T,
    data: &'b mut D,
    mut f: F,
) -> ForceFutureSend<(D, T, R, F), impl Future<Output = R> + Captures<'a> + 'b>
where
    T: for<'x> WithLifetime<'x>,
    F: for<'x> AsyncFnMut3<
        // Wrap<'x, T>,
        <T as WithLifetime<'x>>::Applied,
        Data<'x, D>,
        RecursionContext<'x, T, R>,
        Output = R,
    >,
{
    // let mut result = None;
    // let mut next = None;

    // stupid rust compiler has another bug such that it can't properly evaluate Sendness of this future
    // there is a very ugly workaround for that to work so the future is definitely `Send`
    // in future if there are going to be significant changes here don't forget to check if it still being Send
    ForceFutureSend(
        async move {
            let arg = init;

            let mut ctx_data = WakerData {
                outer_waker: GetOuterWaker.await,
                arg: None::<T>,
                result: None::<R>,
            };
            let waker = waker_with_data(&mut ctx_data);
            let data = Data(AliasableMut::from(data));
            let mut ctx = Context::from_waker(&waker);
            let mut stack = ChainArena::<_, 30>::new();

            stack.push(f.call(
                //SAFETY: same as RefStack
                unsafe { arg.move_with_lifetime() },
                data.copy(),
                RecursionContext(PhantomData),
            ));

            loop {
                // SAFETY: ChainArena does not move elements even when pushed into so it is safe to Pin the element
                // todo make safe api for ChainArena to pin elements
                let fut = unsafe { Pin::new_unchecked(stack.last_mut().unwrap()) };
                let poll = fut.poll(&mut ctx);
                // SAFETY: can't access `ctx_data` directly because in StackedBorrows it would invalidate pointers inside ctx
                let ctx_data = unsafe { get_waker_data::<WakerData<T, R>>(&mut ctx) };
                if let Poll::Ready(returned) = poll {
                    // let returned = unsafe { WithLifetime::move_with_lifetime_back(returned) };
                    stack.pop();
                    if stack.is_empty() {
                        return returned;
                    }
                    ctx_data.result = Some(returned);
                } else {
                    if let Some(arg) = ctx_data.arg.take() {
                        // let ret = Recursion(&next, &result);
                        // let arg = unsafe { core::mem::transmute_copy(&arg) };
                        stack.push(f.call(
                            //SAFETY: same as RefStack
                            unsafe { arg.move_with_lifetime() },
                            data.copy(),
                            RecursionContext(PhantomData),
                        ));
                    } else {
                        // not our return so forward waiting
                        futures_util::pending!();
                    }
                }
            }
        },
        PhantomData,
    )
}
//todo potentially should be more optimized version but something is wrong
// with futures optimizer in rust so it is worse
//
// / Same as [`run_async_backref`] but allows to get access to additional data.
// pub async fn run_async_backref_with_data<'a, F, T, R, D>(init: T, data: &'a mut D, mut f: F) -> R
// where
//     T: for<'x> WithLifetime<'x>,
//     F: for<'x> AsyncFnMut3<
//         <T as WithLifetime<'x>>::Applied,
//         Data<'x, D>,
//         RecursionContext2<'x, T, R>,
//         Output = R,
//     >,
// {
//     // let mut result = None;
//     // let mut next = None;
//     let mut arg = init;
//
//     let mut stack = ChainArena::<_, 30>::new();
//     let data_ptr = data as *mut D;
//     let stack_ptr: *mut _ = &mut stack;
//     // let data = Data(AliasableMut::from(data));
//     let cb_called = Cell::new(false);
//     let cb_called = &cb_called;
//     let mut callback = move |arg: T| unsafe {
//         cb_called.set(true);
//         let fut = f.call(
//             arg.move_with_lifetime(),
//             Data(AliasableMut::from(&mut *data_ptr)),
//             RecursionContext2(PhantomData),
//         );
//         unsafe { &mut *stack_ptr }.push(fut);
//     };
//     fn cast_cb<T>(arg: &mut impl FnMut(T)) -> &mut (dyn 'static + FnMut(T)) {
//         unsafe { core::mem::transmute(arg as &mut dyn FnMut(T)) }
//     }
//
//     let callback_ptr = cast_cb(&mut callback);
//     let mut ctx_data = WakerData2 {
//         callback: callback_ptr,
//         result: MaybeUninit::<R>::uninit(),
//         outer_waker: GetOuterWaker.await,
//     };
//     let waker = waker_with_data(&mut ctx_data);
//     let mut ctx = Context::from_waker(&waker);
//     // let mut ret = RecursionContext::<T, R>(PhantomData);
//     // let mut ret = RecursionRef(AliasableMut::from(&mut ret));
//
//     unsafe {
//         (&mut *callback_ptr)(arg);
//     }
//     loop {
//         //fixme, technically unsound, make ChainArena as actual arena that works via immutable reference
//         let stack = unsafe { &mut *stack_ptr };
//         // SAFETY: ChainArena does not move elements even when pushed into so it is safe to Pin the element
//         let fut = unsafe { Pin::new_unchecked(stack.last_mut().unwrap()) };
//         let poll = fut.poll(&mut ctx);
//         let ctx_data = unsafe { get_waker_data2::<WakerData2<T, R>>(&mut ctx) };
//         if let Poll::Ready(returned) = poll {
//             // let returned = unsafe { WithLifetime::move_with_lifetime_back(returned) };
//             stack.pop();
//             if stack.is_empty() {
//                 return returned;
//             }
//             ctx_data.result.write(returned);
//         } else {
//             if cb_called.get() {
//                 cb_called.set(false);
//                 continue;
//             }
//             //not our return so forward waiting
//             futures_util::pending!();
//         }
//     }
// }

/// Reference to outer data to access from recursive future.
pub struct Data<'a, T>(AliasableMut<'a, T>);
// unsafe impl<'a, T: Send> Send for Data<'a, T> {}
// you can't do anything with shared reference to `Data` so we can always implement Sync
// unsafe impl<'a, T: Send> Sync for Data<'a, T> {}
impl<'a, T> Data<'a, T> {
    fn copy(&self) -> Self {
        //SAFETY: there can't be multiple `Data`s dereferenced at the same time
        // because you can't keep reference to `T` across await points
        unsafe { core::ptr::read(self) }
    }
    /// Reference to `T` must not be held across await point so
    /// the only way to access it is with callback
    pub fn access_with<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        f(&mut self.0)
    }
}

// macro_rules! hrtb_check{
//     ( for<'x,'y> |$arg1:ident : $arg1_ty:ty, $arg1:ident : RecursionRef<'x > | -> ) ={
//
//     }
// }

// pub fn blocking_run_with_backref<'a, F, T, R>(init: T, mut f: F) -> R
//     where
//         T: for<'x> WithLifetime<'x, 'a>,
//         F: for<'x> AsyncFnMut<T, RecursionRef<'x, T, R>, Output=R>,
// {}
//
// pub fn blocking_run_with_backref_inner<'a, F, T, R, Marker>(init: T, mut f: F) -> R
//     where
//         T: for<'x> WithLifetime<'x, 'a, Marker>,
//         R: for<'x> WithLifetime<'x, 'a, Marker>,
//         F: for<'x> AsyncFnMut<
//             <T as WithLifetime<'x, 'a, Marker>>::Applied,
//             RecursionRef<'x, T, R>,
//             Output=<R as WithLifetime<'x, 'a, Marker>>::Applied,
//         >,
// {
//     let waker = futures::task::noop_waker_ref();
//     let mut ctx = std::task::Context::from_waker(waker);
//     let result = Cell::new(None);
//     let next = Cell::new(None);
//
//     let mut stack = ChainArena::<_, 30>::new();
//     let mut arg = init;
//
//     let ret = Recursion(&next, &result);
//     stack.push(f.call(arg, ret));
//     loop {
//         // println!("{}", stack.dbg_len());
//         let poll = unsafe { Pin::new_unchecked(stack.last_mut().unwrap()).poll(&mut ctx) };
//         if let Poll::Ready(returned) = poll {
//             // println!("ready");
//             stack.pop();
//             if stack.is_empty() {
//                 return returned;
//             }
//             result.set(Some(returned));
//         } else {
//             // println!("pending");
//             if let Some(arg) = next.take() {
//                 let ret = Recursion(&next, &result);
//                 // let arg = unsafe { core::mem::transmute_copy(&arg) };
//                 stack.push(f.call(arg, ret));
//             }
//         }
//     }
// }

// pub async fn async_run<F,T,R>(init:T, f: F)
//     where
//         F: for<'x> AsyncFnMut<T, Result<'x, T, R>,Output=R>,
// {
//
// }

/// Helper struct to invoke async recursion
pub type Recursion<'x, T, R> = AliasableMut<'x, RecursionChecked<T, R>>;

#[doc(hidden)]
pub struct RecursionChecked<T, R>(NonNull<Option<T>>, NonNull<Option<R>>);
unsafe impl<T: Send, R: Send> Send for RecursionChecked<T, R> {}
unsafe impl<T: Send, R: Send> Sync for RecursionChecked<T, R> {}

impl<T, R> RecursionChecked<T, R> {
    fn new(next: &mut Option<T>, result: &mut Option<R>) -> Self {
        RecursionChecked(next.into(), result.into())
    }
    fn copy(&self) -> Self {
        RecursionChecked(self.0, self.1)
    }
    /// Invokes recursive async call
    pub fn recurse(&mut self, arg: T) -> impl Future<Output = R> + '_ {
        unsafe {
            *self.0.as_mut() = Some(arg);
        }
        async move {
            // i have no idea why miri requires pointer to be copied before pending!
            // but it passes miri now ¯\_(ツ)_/¯
            let ptr = SendSyncPtr(self.1.as_ptr());
            futures_util::pending!();
            unsafe { (&mut *ptr.0).take().unwrap() }
        }
    }

    /// Prevents moving out `RecursionChecked` from the closure
    pub fn into_return(self, ret: R) -> Checked<R> {
        Checked(ret)
    }
}

/// Marker to indicate that `RecursionChecked` has been consumed.
/// Created by `RecursionChecked::into_return`.
pub struct Checked<R>(R);

// --------------------------------------------------------------------------------------------
//
// unsound because it will be possible to move out reference into previous future
// and previous future will be freed after this function ends, so use after free
// async fn run_async_backref_checked<F, Fut, T, R>(init: T, mut f: F) -> R
// where
//     F: FnMut(PtrMut<T>, RecursionRefChecked<T, R>) -> Fut,
//     Fut: Future<Output = Checked<R>>,
// {
//     todo!()
// }
struct RecursionRefChecked<T, R>(NonNull<Option<T>>, NonNull<Option<R>>);
unsafe impl<T: Send, R: Send> Send for RecursionRefChecked<T, R> {}
unsafe impl<T: Send, R: Send> Sync for RecursionRefChecked<T, R> {}

impl<T, R> RecursionRefChecked<T, R> {
    fn new(next: &mut Option<T>, result: &mut Option<R>) -> Self {
        RecursionRefChecked(next.into(), result.into())
    }
    fn copy(&self) -> Self {
        RecursionRefChecked(self.0, self.1)
    }

    pub fn recurse<'a>(&'a mut self, arg: T::Applied) -> impl Future<Output = R> + 'a
    where
        T: WithLifetime<'a>,
    {
        unsafe {
            *self.0.as_mut() = Some(WithLifetime::move_with_lifetime_back(arg));
        }
        async move {
            futures_util::pending!();
            unsafe { self.1.as_mut().take().unwrap() }
        }
    }

    pub fn into_return<'a, 'b>(self, ret: R, _ptr: PtrMut<T>) -> Checked<R> {
        Checked(ret)
    }
}
struct PtrMut<T>(NonNull<T>);
impl<T> Deref for PtrMut<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}
impl<T> DerefMut for PtrMut<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

// ------------------------------------

#[doc(hidden)]
pub trait Captures<'x> {}
impl<'x, T> Captures<'x> for T {}

/// Helper trait to be able to use HRTBs with async closures
pub trait AsyncFnMut2<T, U> {
    type Future: Future<Output = Self::Output>;
    type Output;
    fn call(&mut self, arg: T, arg2: U) -> Self::Future;
}

impl<T, U, F, R: Future> AsyncFnMut2<T, U> for F
where
    F: FnMut(T, U) -> R,
{
    type Future = R;
    type Output = R::Output;

    fn call(&mut self, arg: T, arg2: U) -> Self::Future {
        self(arg, arg2)
    }
}

/// Helper trait to be able to use HRTBs with async closures
pub trait AsyncFnMut3<T, U, V> {
    type Future: Future<Output = Self::Output>;
    type Output;
    fn call(&mut self, arg: T, arg2: U, arg3: V) -> Self::Future;
}

impl<T, U, V, F, R> AsyncFnMut3<T, U, V> for F
where
    F: FnMut(T, U, V) -> R,
    R: Future,
{
    type Future = R;
    type Output = R::Output;

    fn call(&mut self, arg: T, arg2: U, arg3: V) -> Self::Future {
        self(arg, arg2, arg3)
    }
}

// pub trait AsyncFnOnce<T> {
//     type Future: Future<Output = Self::Output>;
//     type Output;
//     fn call(self, arg: T) -> Self::Future;
// }
//
// impl<T, F, R: Future> AsyncFnOnce<T> for F
// where
//     F: FnOnce(T) -> R,
// {
//     type Future = R;
//     type Output = R::Output;
//
//     fn call(self, arg: T) -> Self::Future {
//         self(arg)
//     }
// }

use core::task::{Context, RawWaker, RawWakerVTable, Waker};

unsafe fn rwclone(ptr: *const ()) -> RawWaker {
    // ideally we should have just copied vtable when creating our Waker
    // but it is impossible to do soundly until `waker_getters` feature stabilized
    // As i understood Waker is always being cloned when being used for waking
    // So if cloning returns suitable Waker then futures that require outer executor
    // will behave properly. So here we invoke clone of saved Waker
    core::mem::transmute((&*(ptr as *const Waker)).clone())
}

unsafe fn rwwake(_p: *const ()) {}

unsafe fn rwwakebyref(_p: *const ()) {}

unsafe fn rwdrop(_p: *const ()) {}

static VTABLE: RawWakerVTable = RawWakerVTable::new(rwclone, rwwake, rwwakebyref, rwdrop);

fn waker_with_data<T>(data: *mut T) -> Waker {
    unsafe { Waker::from_raw(RawWaker::new(data as *mut T as *mut (), &VTABLE)) }
}

/// Continuously poll a future until it returns `Poll::Ready`. This is not normally how an
/// executor should work, because it runs the CPU at 100%.
// pub fn spin_on<F: Future, D>(data: &mut D, future: F) -> F::Output {
//     pin_utils::pin_mut!(future);
//     let waker = &waker_with_data(data);
//     let mut cx = Context::from_waker(waker);
//     loop {
//         if let Poll::Ready(output) = future.as_mut().poll(&mut cx) {
//             return output;
//         }
//     }
// }
struct WakerData2<T, R> {
    outer_waker: Waker,
    callback: *mut dyn FnMut(T),
    result: MaybeUninit<R>,
}

struct RecursionContext2<'a, T, R>(PhantomData<*mut &'a mut (T, R)>);
impl<'x, T, R> RecursionContext2<'x, T, R> {
    pub fn recurse<'a, Out: 'a>(&'a mut self, arg: Out) -> impl Future<Output = R> + 'a
    where
        T: WithLifetime<'a, Applied = Out>,
    {
        // let state = false;
        // let mut arg = ManuallyDrop::new(arg);
        async move {
            // if state {
            let callback = futures_util::future::poll_fn(|ctx| {
                Poll::Ready(unsafe { get_waker_data::<WakerData2<T, R>>(ctx).callback })
            })
            .await;
            unsafe { (&mut *callback)(WithLifetime::move_with_lifetime_back(arg)) };
            futures_util::pending!();
            // } else {
            futures_util::future::poll_fn(|ctx| {
                Poll::Ready(unsafe {
                    get_waker_data::<WakerData2<T, R>>(ctx)
                        .result
                        .as_ptr()
                        .read()
                })
            })
            .await
            // unsafe { data.result.assume_init_read() }
            // }
        }
    }
}

struct WakerData<T, R> {
    outer_waker: Waker,
    arg: Option<T>,
    // todo, no need for option, check if MaybeUninit actually improves something
    result: Option<R>,
}

/// Helper struct to invoke async recursion with references to previous state
pub struct RecursionContext<'a, T, R>(PhantomData<fn(&'a mut (T, R)) -> &'a ()>);

impl<'x, T, R> RecursionContext<'x, T, R> {
    pub fn recurse<'a>(&'a mut self, arg: T::Applied) -> RecursionFuture<'a, T::Applied, R>
    where
        T: WithLifetime<'a>,
    {
        RecursionFuture(Some(arg), PhantomData)
    }
}

/// Future returned from [`RecursionContext::recurse`]
pub struct RecursionFuture<'a, T, R>(Option<T>, PhantomData<PhantomData<fn(&'a mut R) -> &'a ()>>);
impl<'x, T: Unpin, R> Future for RecursionFuture<'x, T, R> {
    type Output = R;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: because of HRTB lifetime we know that we are inside `run_async*` call
        // so `WakerData` is valid
        // but when in future scoped async will be a thing it would be possible to cause UB
        // but we can prevent it by checking that we are still in suitable context via
        // ptr::eq(cx.waker().as_raw().vtable(),&VTABLE);
        // although it currently requires nightly features so it is not enabled right now
        let data = unsafe { get_waker_data::<WakerData<T, R>>(cx) };

        if let t @ Some(_) = self.0.take() {
            data.arg = t;
            Poll::Pending
        } else {
            Poll::Ready(data.result.take().unwrap())
        }
    }
}

unsafe fn get_waker_data<'a, D>(cx: &'a mut Context<'_>) -> &'a mut D {
    // technically not guaranteed to sound,
    // but it's a temporary solution until waker_getters feature is stabilized
    &mut **(cx.waker() as *const _ as *const *mut D)
}

struct GetOuterWaker;
impl Future for GetOuterWaker {
    type Output = Waker;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(cx.waker().clone())
    }
}

// /// Struct to delegate future to the outer executor
// pub struct WithExecutor<Fut, T, R>(pub Fut, WakerData<T, R>);
// impl<Fut: Future, T, R> Future for WithExecutor<Fut, T, R> {
//     type Output = Fut::Output;
//
//     fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
//         let (inner, data) = unsafe {
//             let this = self.get_unchecked_mut();
//             (Pin::new_unchecked(&mut this.0), &mut this.1)
//         };
//         let outer_waker = cx.waker().clone();
//         data.outer_waker = outer_waker;
//         let waker = waker_with_data(data);
//         let mut ctx = Context::from_waker(&waker);
//         inner.poll(&mut ctx)
//     }
// }

/// Indicates what action should be performed on stack afterwards
pub enum Action<T, Y = (), R = ()> {
    /// Pushes state to the internal stack. Equivalent of doing a recursive call.
    Recurse(T),
    /// Stops everything and yields from whole recursion process.
    /// Whether the current stack is preserved depends on a function being used.
    Yield(Y),
    /// Pops state from stack. Equivalent of returning from recursion call.
    Return(R),
}

struct ChainArena<T, const CHUNK_SIZE: usize> {
    // filled: Cell<usize>,
    buf: arrayvec::ArrayVec<T, CHUNK_SIZE>,
    next: Option<Box<Self>>,
}

impl<T, const CHUNK_SIZE: usize> ChainArena<T, CHUNK_SIZE> {
    fn new() -> Self {
        Self {
            buf: arrayvec::ArrayVec::new(),
            next: None,
        }
    }

    fn push(&mut self, el: T) {
        self.buf.try_push(el).unwrap_or_else(|e| {
            if let Err(err) = self
                .next
                .get_or_insert_with(|| Box::new(Self::new()))
                .buf
                .try_push(e.element())
            {
                let next = self.next.replace(Box::new(Self::new()));
                self.next.as_deref_mut().unwrap().next = next;
                self.next
                    .as_deref_mut()
                    .unwrap()
                    .buf
                    .try_push(err.element())
                    .expect("should be able to push in empty ArrayVec");
            }
        });
    }

    fn pop(&mut self) -> Option<T> {
        // let buf = &mut self.buf;

        let tmp = self
            .next
            .as_deref_mut()
            .and_then(|x| x.buf.pop())
            .or_else(|| self.buf.pop());

        if let Some(next) = self.next.as_deref_mut() {
            if next.buf.len() == 0 {
                let tmp = self.next.take();
                self.next = tmp.unwrap().next.take();
            }
        }
        tmp
    }

    fn last_mut(&mut self) -> Option<&mut T> {
        self.next
            .as_deref_mut()
            .and_then(|x| x.buf.last_mut())
            .or_else(|| self.buf.last_mut())
    }

    fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }

    fn dbg_len(&self) -> usize {
        self.buf.len() + self.next.as_ref().map_or(0, |x| x.dbg_len())
    }
}

// explicit Drop exists to drop stuff in reverse order
impl<T, const CHUNK_SIZE: usize> Drop for ChainArena<T, CHUNK_SIZE> {
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }
}

#[cfg(test)]
mod test {
    use crate::ChainArena;

    #[test]
    fn test_cap1() {
        test_cap::<1>();
        test_cap::<2>();
        test_cap::<10>();
        test_cap::<20>();
    }

    fn test_cap<const SIZE: usize>() {
        let mut x = ChainArena::<_, SIZE>::new();
        for i in 0..10 {
            x.push(i);
            assert_eq!(*x.last_mut().unwrap(), i);
        }

        for i in (0..10).rev() {
            assert_eq!(*x.last_mut().unwrap(), i);
            assert_eq!(x.pop(), Some(i));
        }
    }
}
//
// pub trait MyFnOnce<T> {
//     type Output;
//
//     fn call(self, arg: T) -> Self::Output;
// }
//
// impl<T, F, O> MyFnOnce<T> for F
// where
//     F: FnOnce(T) -> O,
// {
//     type Output = O;
//
//     fn call(self, arg: T) -> Self::Output {
//         self(arg)
//     }
// }

// struct BorrowHList<'a, Head, Tail>(pub Head, MaybeUninit<Tail>);
//
// struct Nil;
//
// impl<'a, H> BorrowHList<'a, H, Nil> {
//     pub fn new(first: H) -> Self {
//         Self(first, Nil, PhantomData)
//     }
// }
//
// impl<'a, H, T> BorrowHList<'a, H, T> {
//     pub fn push_with<F, R>(self, next: F) -> BorrowHList<'a, R, Self>
//     where
//         H: for<'x> WithLifetime<'x, 'a>,
//         R: for<'x> WithLifetime<'x, 'a>,
//         F: FnOnce(&'a mut H) -> R + 'static,
//     {
//         BorrowHList()
//     }
//
//     pub fn pop(self) -> T {
//         unsafe { self.1.assume_init() }
//     }
// }

// todo add marker to allow implementations on foreign traits
/// Trait to be able to apply HRTBs to arbitrary types
/// Can be safely implemented by users for their own types.
/// Soundness is ensured by the sealed `Check` trait which is implemented in a way
/// that allows only correct `WithLifetime` implementations.
///
/// Note that if multiple lifetimes are involved the lifetime that is being changed must be the smallest one.
/// You might need to add corresponding bounds when implementing it.
/// It is a temporary limitation caused by a compiler bug.
/// For example notice additional `'b: 'this` here that makes sure that `'this` is smallest lifetime here.
/// ```rust
/// # use unrecurse::{Lifetime, WithLifetime};
/// struct Test<'a, 'b>(&'a (),&'b ());
/// impl<'applied, 'this, 'b: 'this> WithLifetime<'applied> for Test<'this, 'b> {
///     type Lifetime = Lifetime<'this>;
///     type Applied = Test<'applied, 'b>;
/// }
///
/// fn test<T: for<'x> WithLifetime<'x>>() {}
/// fn call<'a, 'b: 'a>() {
///     test::<Test<'a, 'b>>();
/// }
/// ```
/// It does impose some limitations(in this case `'b: 'a` bound on `call` that shouldn't be needed),
/// but in practice it is pretty rare to cause actual problems.
pub trait WithLifetime<'a, T = &'a Self>: Check<Self::Lifetime> /*+ HasGeneric*/ {
    /// There is no way to have an associated lifetime in Rust.
    /// This type acts as a workaround for that.
    /// [`Lifetime`] struct is the only suitable type here.
    type Lifetime: LifetimeMarker;
    /// This should be a `Self` but with [`Self::Lifetime`] lifetime changed to `'a`.
    /// Otherwise you will get a compile error
    type Applied;
    #[doc(hidden)]
    unsafe fn with_lifetime(&self) -> &Self::Applied {
        transmute_copy(&self)
    }

    #[doc(hidden)]
    unsafe fn with_lifetime_mut(mut self: &mut Self) -> &mut Self::Applied {
        transmute_copy(&mut self)
    }

    #[doc(hidden)]
    unsafe fn move_with_lifetime(self) -> Self::Applied
    where
        Self: Sized,
        Self::Applied: Sized,
    {
        let this = ManuallyDrop::new(self);
        let res = transmute_copy(&*this);
        res
    }

    #[doc(hidden)]
    unsafe fn move_with_lifetime_back(this: Self::Applied) -> Self
    where
        Self: Sized,
        Self::Applied: Sized,
    {
        let this = ManuallyDrop::new(this);
        let res = transmute_copy(&*this);
        res
    }
}

/// Type that represents associated lifetime in [`WithLifetime::Lifetime`]
pub struct Lifetime<'a>(PhantomData<*mut &'a ()>);

use private::Check;
use private::LifetimeMarker;

mod private {
    use super::*;

    pub trait LifetimeMarker {}
    impl<'a> LifetimeMarker for Lifetime<'a> {}

    pub trait Check<L: LifetimeMarker> {}
    impl<'b, T> Check<Lifetime<'b>> for T where
        T: WithLifetime<'b, Lifetime = Lifetime<'b>, Applied = Self> + 'b // <T as HasGeneric>::Generic: 'b,
    {
    }
}

// usable with HRTBs,
// /// Due to bug in compiler HRTB with `WithLifetime` trait does not work,
// /// so workaround is to use a separate trait with implied weaker bounds.
// /// Unfortunately due to another bug in compiler blanket implementation of that trait also does not work properly.
// /// So you need to duplicate the implementation of `WithLifetime` for `ShrinkLifetime`.
// ///
// ///
// pub trait ShrinkLifetime<'a, T = &'a <Self as HasGeneric>::Generic>:
//     WithLifetime<Lifetime<'a>, Applied = Self::BoundApplied> + HasGeneric
// // + WithLifetime<Lifetime<'a>, Lifetime = Lifetime<'a>, Applied = Self>
// {
//     type BoundApplied: WithLifetime<Self::Lifetime, Lifetime = Lifetime<'a>, Applied = Self>;
// }

// trait ShrinkLifetime<'a>: WithLifetime<Lifetime<'a>> {
//     type BoundApplied: WithLifetime<Self::Lifetime, Lifetime = Lifetime<'a>, Applied = Self>;
// }

// /// Workaround for some compiler limitations when checking HRTBs.
// pub trait HasGeneric {
//     /// This should be a tuple of generics that are bound by the lifetime you are going to change in `WithLifetime`
//     /// Otherwise you will get a ``error[E0311]: the parameter type `T` may not live long enough``
//     /// E.g. if you have `&'a mut T` and you are changing `'a` lifetime, then `Generic` should be `T`
//     /// if you have `&'a &'b()` and you are changing `'a` lifetime, then `Generic` should be
//     /// some type with `'b` lifetime, for example `&'b ()`.
//     /// Note that in latter case due to compiler bugs you will need to explicitly write out generic
//     /// parameter of `Withlifetime` trait.
//     /// ```text
//     /// impl<'a,'b,'new> WithLifetime<'new,&'new &'b ()> for &'a &'b (){
//     /// ```
//     type Generic;
// }
// pub trait ImplicitBound<'a, T = &'a <Self as HasGeneric>::Generic>: HasGeneric {}
// impl<'a, T: HasGeneric> ImplicitBound<'a> for T {}

// pub trait ImplicitGeneric<T: LifetimeMarkerExt<Self>,> {}

// impl<'a, T, Appl> ShrinkLifetime<'a> for T
// where
//     T: WithLifetime<Lifetime<'a>, Applied = Appl>,
//     Appl: WithLifetime<Self::Lifetime, Lifetime = Lifetime<'a>, Applied = Self>,
// {
//     type BoundApplied = Appl;
// }

// pub unsafe trait Tid<'a>: 'a {
//     fn self_id(&self) -> TypeId;
//     fn id() -> TypeId
//     where
//         Self: Sized;
// }

// unsafe impl<'a, T: 'a> Tid<'a> for T
// where
//     T: WithLifetime<Lifetime<'static>, Lifetime = Lifetime<'a>>,
//     <T as WithLifetime<Lifetime<'static>>>::Applied: 'static
// {
//     fn self_id(&self) -> TypeId {
//         Self::id()
//     }
//     fn id() -> TypeId
//     where
//         Self: Sized,
//     {
//         TypeId::of::<T::Applied>()
//     }
// }

// trait WithLifetimeSuper<'a>: WithLifetime<'a> + WithLifetimeGeneric<>

impl<'applied, 'this, T> WithLifetime<'applied> for &'this T {
    type Lifetime = Lifetime<'this>;
    type Applied = &'applied T;
}
//
// impl<'this, T> HasGeneric for &'this T {
//     type Generic = (T);
// }
// impl<'a, 'this, T> ShrinkLifetime<'a> for &'this T {
//     type BoundApplied = &'a T;
// }

impl<'applied, 'this, T> WithLifetime<'applied> for &'this mut T {
    type Lifetime = Lifetime<'this>;
    type Applied = &'applied mut T;
}

// impl<'this, T> HasGeneric for &'this mut T {
//     type Generic = T;
// }
// impl<'a, 'this, T> ShrinkLifetime<'a> for &'this mut T {
//     type BoundApplied = &'a mut T;
// }

impl<'applied> WithLifetime<'applied> for () {
    type Lifetime = Lifetime<'applied>;
    type Applied = ();
}

// impl HasGeneric for () {
//     type Generic = ();
// }
// impl<'a> ShrinkLifetime<'a> for () {
//     type BoundApplied = ();
// }

macro_rules! std_impl {
    ($($type:tt)+) => {
        impl<'a, 'this,T> WithLifetime<'a> for $($type)+<'this, T> {
            type Lifetime = Lifetime<'this>;
            type Applied = $($type)+<'a, T>;
        }
    };
}

std_impl! {core::cell::Ref}
std_impl! {core::cell::RefMut}
std_impl! {std::sync::MutexGuard}
std_impl! {std::sync::RwLockReadGuard}
std_impl! {std::sync::RwLockWriteGuard}

// this was initial idea but it had two lifetimes which created some problems
// but it more clearly represents the idea so
mod old {
    /// Trait that indicates that the type has a lifetime and that lifetime can be manipulated in type-system.
    /// Sealed `Check` trait allows `WithLifetime` to be a safe to implement trait.
    ///
    /// `Marker` type parameter allows to implement `WithLifetime` on foreign traits by defining your own marker type.
    /// But it is not yet used by this crate so just ignore it for now.
    pub trait WithLifetime<'applied, 'this, Marker = ()/*, const LIFETIME_INDEX: usize = 0*/>:
    Check<'this, Marker>
    {
        /// This should be a `Self` but with `'this` lifetime changed to `'applied`
        type Applied: WithLifetime<'this, 'applied, Marker, Applied=Self>;

        #[doc(hidden)]
        unsafe fn with_lifetime(&self) -> &Self::Applied {
            transmute_copy(&self)
        }

        #[doc(hidden)]
        unsafe fn with_lifetime_mut(mut self: &mut Self) -> &mut Self::Applied {
            transmute_copy(&mut self)
        }

        #[doc(hidden)]
        unsafe fn move_with_lifetime(self) -> Self::Applied
            where
                Self: Sized,
                Self::Applied: Sized,
        {
            let this = ManuallyDrop::new(self);
            let res = transmute_copy(&*this);
            res
        }

        #[doc(hidden)]
        unsafe fn move_with_lifetime_back(this: Self::Applied) -> Self
            where
                Self: Sized,
                Self::Applied: Sized,
        {
            let this = ManuallyDrop::new(this);
            let res = transmute_copy(&*this);
            res
        }
    }

    use private::Check;
    use std::mem::{transmute_copy, ManuallyDrop};

    mod private {
        pub trait Check<'a, Marker>: 'a {}

        impl<'a, Marker, T /*+ ?Sized*/> Check<'a, Marker> for T where
            T: super::WithLifetime<'a, 'a, Marker, Applied = Self>
        {
        }
    }

    impl<'applied, 'this, T> WithLifetime<'applied, 'this> for &'this T
    where
        T: 'applied + 'this,
    {
        type Applied = &'applied T;
    }

    impl<'applied, 'this> WithLifetime<'applied, 'this> for () {
        type Applied = ();
    }

    impl<'applied, 'this, T: 'applied + 'this> WithLifetime<'applied, 'this> for &'this mut T {
        type Applied = &'applied mut T;
    }

    struct Identity;

    impl<'applied, 'this, T: 'applied + 'this> WithLifetime<'applied, 'this, Identity> for T {
        type Applied = T;
    }
}

// trait BorrowStack<'a> {
//     fn push()
// }

// impl<T,M> Index<usize> for RefStack<'_, T,M>{
//     type Output = M;
//
//     fn index(&self, index: usize) -> &Self::Output {
//         unsafe { &*self.metadata[index] }
//     }
// }
// impl<T,M> IndexMut<usize> for RefStack<'_, T,M>{
//     fn index_mut(&mut self, index: usize) -> &mut Self::Output {
//         unsafe { &mut *self.metadata[index] }
//     }
// }

//temporary copy from `aliasable` until they publish fixed version
#[doc(hidden)]
pub struct AliasableMut<'a, T: ?Sized> {
    inner: NonNull<T>,
    _lifetime: PhantomData<&'a mut T>,
}

impl<'a, T: ?Sized> AliasableMut<'a, T> {
    /// Construct an `AliasableMut` from an `&mut`.
    #[inline]
    pub fn from_unique(ptr: &'a mut T) -> Self {
        Self {
            inner: NonNull::from(ptr),
            _lifetime: PhantomData,
        }
    }
}
impl<'a, T: ?Sized> From<&'a mut T> for AliasableMut<'a, T> {
    fn from(ptr: &'a mut T) -> Self {
        Self::from_unique(ptr)
    }
}

impl<T: ?Sized> Deref for AliasableMut<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY: It is the callers responsibility to make sure that there are no `&mut`
        // references at this point.
        unsafe { self.inner.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for AliasableMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: It is the callers responsibility to make sure that there are no `&mut`
        // references at this point.
        unsafe { self.inner.as_mut() }
    }
}
unsafe impl<T: ?Sized> Send for AliasableMut<'_, T> where T: Send {}
unsafe impl<T: ?Sized> Sync for AliasableMut<'_, T> where T: Sync {}
