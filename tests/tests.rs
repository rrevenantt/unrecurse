use std::future::Future;
use unrecurse::{Action, Lifetime, Recursion, RecursionContext, RefStack, WithLifetime};

#[derive(Default, Debug, Clone, Eq, PartialEq)]
struct BinaryTree {
    v: i32,
    left: Option<Box<BinaryTree>>,
    right: Option<Box<BinaryTree>>,
}

impl BinaryTree {
    fn invert(&mut self) {
        let mut stack = RefStack::<_, (bool, bool)>::new(self);

        loop {
            if *stack.meta() == (true, true) {
                let left = stack.current().left.take();
                let right = stack.current().right.take();
                stack.current().right = left;
                stack.current().left = right;

                stack.pop();
                if stack.len() == 0 {
                    return;
                }
                continue;
            }

            let have_been_right = stack.meta().1;
            stack.meta().1 = true;

            if stack.current().right.is_some() && !have_been_right {
                stack.push_with(|this| this.right.as_deref_mut().unwrap());
                continue;
            }

            let have_been_left = stack.meta().0;
            stack.meta().0 = true;

            if stack.current().left.is_some() && !have_been_left {
                stack.push_with(|this| this.left.as_deref_mut().unwrap());
                continue;
            }
        }
    }
    fn invert4(&mut self) {
        struct State<'a>(bool, bool, &'a mut BinaryTree);
        impl<'a> State<'a> {
            fn new(from: &'a mut BinaryTree) -> Self {
                Self(false, false, from)
            }
        }
        impl<'a, 'b> WithLifetime<'a> for State<'b> {
            type Lifetime = Lifetime<'b>;
            type Applied = State<'a>;
        }

        // impl<'a, 'b> ShrinkLifetime<'a> for State<'b> {
        //     type BoundApplied = State<'a>;
        // }

        unrecurse::run(State(false, false, self), |state| {
            if let State(true, true, _) = state {
                let left = state.2.left.take();
                let right = state.2.right.take();
                state.2.right = left;
                state.2.left = right;

                return Action::Return(());
            }

            let have_been_right = state.1;
            state.1 = true;

            if state.2.right.is_some() && !have_been_right {
                return Action::Recurse(State::new(state.2.right.as_deref_mut().unwrap()));
            }

            let have_been_left = state.0;
            state.0 = true;

            if state.2.left.is_some() && !have_been_left {
                return Action::Recurse(State::new(state.2.left.as_deref_mut().unwrap()));
            }
            Action::Return(())
        })
    }

    // fn invert3(&mut self) {
    //     let mut stack = GenericRefStack::<(bool, bool, &mut Self)>::new((false, false, self));
    //     self::pin_mut!(stack);
    //
    //     loop {
    //         // println!("{} {}", stack.len(), stack.current().2.v);
    //         if let (true, true, current) = stack.current() {
    //             let left = current.left.take();
    //             let right = current.right.take();
    //             current.right = left;
    //             current.left = right;
    //
    //             stack.pop();
    //             if stack.is_empty() {
    //                 return;
    //             }
    //             continue;
    //         }
    //
    //         let have_been_right = stack.current().1;
    //         stack.current().1 = true;
    //
    //         fn helper<F>(f: F) -> F
    //         where
    //             F: for<'a, 'b> FnOnce(
    //                 &'a mut (bool, bool, &'b mut BinaryTree),
    //             ) -> (bool, bool, &'a mut BinaryTree),
    //         {
    //             f
    //         }
    //
    //         if stack.current().2.right.is_some() && !have_been_right {
    //             // stack.push_with2(helper(|this| {
    //             //     (false, false, this.2.right.as_deref_mut().unwrap())
    //             // }));
    //             stack
    //                 .push_with(|this: &mut _| (false, false, this.2.right.as_deref_mut().unwrap()));
    //             continue;
    //         }
    //
    //         let have_been_left = stack.current().0;
    //         stack.current().0 = true;
    //
    //         if stack.current().2.left.is_some() && !have_been_left {
    //             stack.push_with(|this| (false, false, this.2.left.as_deref_mut().unwrap()));
    //             continue;
    //         }
    //     }
    // }

    fn invert3(&mut self) {
        // fn test<F,Fut>(f:F) -> F where F:for<'x> FnMut() -> Fut{f}
        async fn inner<'a>(
            // mut arg: Wrap<'_, &'b mut BinaryTree>,
            mut arg: &'_ mut BinaryTree,
            mut rec: RecursionContext<'_, &'a mut BinaryTree, ()>,
        ) {
            if let Some(left) = &mut arg.left {
                rec.recurse(left).await;
                // futures_util::pending!()
            }
            if let Some(right) = &mut arg.right {
                rec.recurse(right).await;
                // futures_util::pending!()
            }
            let left = arg.left.take();
            let right = arg.right.take();
            arg.right = left;
            arg.left = right;
        }
        test_send(unrecurse::run_async_backref(&mut *self, inner));
        // test_send(inner(self, RecursionContext(PhantomData)));
        futures_executor::block_on(unrecurse::run_async_backref(self, inner));
    }

    fn invert2(&mut self) {
        let mut stack = vec![self];
        loop {
            let current = if let Some(x) = stack.pop() {
                x
            } else {
                return;
            };
            let left = current.left.take();
            let right = current.right.take();
            current.right = left;
            current.left = right;

            if let Some(left) = &mut current.left {
                stack.push(left.as_mut())
            }
            if let Some(right) = &mut current.right {
                stack.push(right.as_mut())
            }
        }
    }
}

#[test]
fn test_invert() {
    invert(BinaryTree::invert);
    invert(BinaryTree::invert2);
    invert(BinaryTree::invert3);
    invert(BinaryTree::invert4);
}

fn invert(invert: impl FnOnce(&mut BinaryTree)) {
    let mut bt = BinaryTree {
        v: 1,
        left: Some(Box::new(BinaryTree {
            v: 4,
            left: None,
            right: None,
        })),
        right: Some(Box::new(BinaryTree {
            v: 2,
            left: Some(Box::new(BinaryTree {
                v: 5,
                left: None,
                right: None,
            })),
            right: Some(Box::new(BinaryTree {
                v: 3,
                left: None,
                right: None,
            })),
        })),
    };

    invert(&mut bt);
    assert_eq!(
        bt,
        BinaryTree {
            v: 1,
            left: Some(Box::new(BinaryTree {
                v: 2,
                left: Some(Box::new(BinaryTree {
                    v: 3,
                    left: None,
                    right: None,
                })),
                right: Some(Box::new(BinaryTree {
                    v: 5,
                    left: None,
                    right: None
                }))
            })),
            right: Some(Box::new(BinaryTree {
                v: 4,
                left: None,
                right: None
            }))
        }
    );
}

fn test_send<T: Future + Send>(_t: T) {}
#[test]
fn test_async() {
    async fn fib(n: u32, mut rec: Recursion<'_, u32, u64>) -> u64 {
        // async fn fib(n : u32) -> u64 {
        match n {
            0 => panic!("zero is not a valid argument to fib()!"),
            1 | 2 => 1,
            3 => 2,
            _ => rec.recurse(n - 1).await + rec.recurse(n - 2).await,
        }
    }
    assert_eq!(unrecurse::run_async_blocking(5, fib), 5);

    let result = futures_executor::block_on(unrecurse::run_async(5, fib));
    assert_eq!(result, 5);

    test_send(unrecurse::run_async(5, fib));
    // test(RecursionChecked::<u32, u64>(NonNull::dangling(), NonNull::dangling()).recurse(4));
}

mod avl {
    // Copied from https://github.com/FrancisMurillo/avl_tree_set_rs
    // so code in this module is available under `GPL-3.0 License` as in original repo

    use std::cmp::Ordering;
    use std::iter::FromIterator;
    use std::mem::replace;

    #[derive(Debug, PartialEq, Clone)]
    pub struct AvlTreeSet<T: Ord> {
        root: AvlTree<T>,
    }

    impl<T: Ord> Default for AvlTreeSet<T> {
        fn default() -> Self {
            Self { root: None }
        }
    }

    impl<T: Ord> AvlTreeSet<T> {
        pub fn new() -> Self {
            Self { root: None }
        }

        pub fn insert(&mut self, value: T) -> bool {
            // let mut prev_ptrs = RefStack::<_, ()>::new(&mut self.root);
            // struct Marker;
            // impl<'a, 'b, T: Ord + 'a> WithLifetime<'a, 'b, Marker> for &'b mut AvlTree<T> {
            //     type Applied = &'a mut AvlTree<T>;
            // }

            let mut value = Some(value);
            unrecurse::run(&mut self.root, |state| {
                // let mut current_tree = &mut self.root;
                let state = state.deref_mut();
                if value.is_some() {
                    if let Some(current_node) = state {
                        // prev_ptrs.push(&mut **current_node);

                        return match current_node.value.cmp(value.as_ref().unwrap()) {
                            Ordering::Less => Action::Recurse(&mut current_node.right),
                            // Ordering::Less => Action::Recurse(&mut current_node.right),
                            Ordering::Equal => Action::Yield(true),
                            Ordering::Greater => Action::Recurse(&mut current_node.left),
                            // Ordering::Greater => Action::Recurse(&mut current_node.left),
                        };
                    }

                    *state = Some(Box::new(AvlNode {
                        value: value.take().unwrap(),
                        left: None,
                        right: None,
                        height: 1,
                    }));
                }

                // while let Some(Some(node)) = prev_ptrs.pop() {
                // let node = unsafe { &mut *node_ptr };
                state.as_mut().unwrap().update_height();
                state.as_mut().unwrap().rebalance();
                // }
                Action::Return(())
            })
            .not()
        }

        pub fn take(&mut self, value: &T) -> Option<T> {
            // let mut prev_ptrs = Vec::<*mut AvlNode<T>>::new();
            let mut prev_ptrs = RefStack::<_, ()>::new(&mut self.root);
            // let mut current_tree = &mut self.root;
            // let mut target_value = None;

            // unrecurse::run_checked(&mut self.root, |arg| {
            // if target_value.is_none() {
            while let Some(current_node) = prev_ptrs.current() {
                match current_node.value.cmp(&value) {
                    Ordering::Less => {
                        prev_ptrs.push_with(|cur| &mut cur.as_deref_mut().unwrap().right);
                    }
                    Ordering::Equal => {
                        // target_value = Some(&mut **current_node);
                        break;
                    }
                    Ordering::Greater => {
                        prev_ptrs.push_with(|cur| &mut cur.as_deref_mut().unwrap().left);
                    }
                };
            }
            // }

            let target_node = if let Some(Some(curr)) = prev_ptrs.pop() {
                &mut **curr
            } else {
                return None;
            };

            let taken_value = if target_node.left.is_none() || target_node.right.is_none() {
                if let Some(left_node) = target_node.left.take() {
                    replace(target_node, *left_node).value
                } else if let Some(right_node) = target_node.right.take() {
                    replace(target_node, *right_node).value
                } else if let Some(Some(prev_node)) = prev_ptrs.pop() {
                    // let prev_node = unsafe { &mut *prev_ptr };

                    let inner_value = if let Some(left_node) = prev_node.left.as_ref() {
                        if left_node.value == *value {
                            prev_node.left.take().unwrap().value
                        } else {
                            prev_node.right.take().unwrap().value
                        }
                    } else {
                        prev_node.right.take().unwrap().value
                    };

                    prev_node.update_height();
                    prev_node.rebalance();

                    inner_value
                } else {
                    return self.root.take().map(|x| x.value);
                }
            } else {
                let right_tree = &mut target_node.right;

                if right_tree.as_ref().unwrap().left.is_none() {
                    let mut right_node = right_tree.take().unwrap();

                    let inner_value = replace(&mut target_node.value, right_node.value);
                    // replace(&mut target_node.right, right_node.right.take());
                    target_node.right = right_node.right.take();

                    target_node.update_height();
                    target_node.rebalance();

                    inner_value
                } else {
                    let next_tree = right_tree;
                    // let mut inner_ptrs = Vec::<*mut AvlNode<T>>::new();
                    let mut inner_ptrs = RefStack::<_, ()>::new(next_tree.as_deref_mut().unwrap());

                    while inner_ptrs.current().left.is_some() {
                        inner_ptrs.push_with(|x| x.left.as_deref_mut().unwrap())
                    }
                    inner_ptrs.pop();

                    let parent_left_node = inner_ptrs.pop().unwrap();
                    let mut leftmost_node = parent_left_node.left.take().unwrap();

                    let inner_value = replace(&mut target_node.value, leftmost_node.value);
                    parent_left_node.left = leftmost_node.right.take();

                    parent_left_node.update_height();
                    parent_left_node.rebalance();

                    while let Some(node) = inner_ptrs.pop() {
                        // let node = unsafe { &mut *node_ptr };
                        node.update_height();
                        node.rebalance();
                    }

                    target_node.update_height();
                    target_node.rebalance();

                    inner_value
                }
            };

            while let Some(Some(node)) = prev_ptrs.pop() {
                // let node = unsafe { &mut *node_ptr };
                node.update_height();
                node.rebalance();
            }

            Some(taken_value)
            // })
        }
    }

    // use futures::sink::With;
    use std::cmp::max;
    use std::mem::swap;
    use std::ops::{DerefMut, Not};
    use unrecurse::{Action, RefStack};

    #[derive(Debug, PartialEq, Clone)]
    pub struct AvlNode<T: Ord> {
        pub value: T,
        pub left: AvlTree<T>,
        pub right: AvlTree<T>,
        pub height: usize,
    }

    pub type AvlTree<T> = Option<Box<AvlNode<T>>>;

    impl<'a, T: 'a + Ord> AvlNode<T> {
        pub fn left_height(&self) -> usize {
            self.left.as_ref().map_or(0, |left| left.height)
        }

        pub fn right_height(&self) -> usize {
            self.right.as_ref().map_or(0, |right| right.height)
        }

        pub fn update_height(&mut self) {
            self.height = 1 + max(self.left_height(), self.right_height());
        }

        pub fn balance_factor(&self) -> i8 {
            let left_height = self.left_height();
            let right_height = self.right_height();

            if left_height >= right_height {
                (left_height - right_height) as i8
            } else {
                -((right_height - left_height) as i8)
            }
        }

        pub fn rotate_left(&mut self) -> bool {
            if self.right.is_none() {
                return false;
            }

            let right_node = self.right.as_mut().unwrap();
            let right_left_tree = right_node.left.take();
            let right_right_tree = right_node.right.take();

            let mut new_left_tree = replace(&mut self.right, right_right_tree);
            swap(&mut self.value, &mut new_left_tree.as_mut().unwrap().value);
            let left_tree = self.left.take();

            let new_left_node = new_left_tree.as_mut().unwrap();
            new_left_node.right = right_left_tree;
            new_left_node.left = left_tree;
            self.left = new_left_tree;

            if let Some(node) = self.left.as_mut() {
                node.update_height();
            }

            self.update_height();

            true
        }

        pub fn rotate_right(&mut self) -> bool {
            if self.left.is_none() {
                return false;
            }

            let left_node = self.left.as_mut().unwrap();
            let left_right_tree = left_node.right.take();
            let left_left_tree = left_node.left.take();

            let mut new_right_tree = replace(&mut self.left, left_left_tree);
            swap(&mut self.value, &mut new_right_tree.as_mut().unwrap().value);
            let right_tree = self.right.take();

            let new_right_node = new_right_tree.as_mut().unwrap();
            new_right_node.left = left_right_tree;
            new_right_node.right = right_tree;
            self.right = new_right_tree;

            if let Some(node) = self.right.as_mut() {
                node.update_height();
            }

            self.update_height();

            true
        }

        pub fn rebalance(&mut self) -> bool {
            match self.balance_factor() {
                -2 => {
                    let right_node = self.right.as_mut().unwrap();

                    if right_node.balance_factor() == 1 {
                        right_node.rotate_right();
                    }

                    self.rotate_left();

                    true
                }

                2 => {
                    let left_node = self.left.as_mut().unwrap();

                    if left_node.balance_factor() == -1 {
                        left_node.rotate_left();
                    }

                    self.rotate_right();

                    true
                }
                _ => false,
            }
        }
    }

    #[derive(Debug)]
    pub struct AvlTreeSetNodeIter<'a, T: Ord> {
        prev_nodes: Vec<&'a AvlNode<T>>,
        current_tree: &'a AvlTree<T>,
    }

    impl<'a, T: 'a + Ord> Iterator for AvlTreeSetNodeIter<'a, T> {
        type Item = &'a AvlNode<T>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                match *self.current_tree {
                    None => match self.prev_nodes.pop() {
                        None => {
                            return None;
                        }

                        Some(ref prev_node) => {
                            self.current_tree = &prev_node.right;

                            return Some(prev_node);
                        }
                    },

                    Some(ref current_node) => {
                        if current_node.left.is_some() {
                            self.prev_nodes.push(&current_node);
                            self.current_tree = &current_node.left;

                            continue;
                        }

                        if current_node.right.is_some() {
                            self.current_tree = &current_node.right;

                            return Some(current_node);
                        }

                        self.current_tree = &None;

                        return Some(current_node);
                    }
                }
            }
        }
    }

    impl<T: Ord> FromIterator<T> for AvlTreeSet<T> {
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            let mut set = Self::new();

            for i in iter {
                set.insert(i);
            }

            set
        }
    }

    #[cfg(all(test, not(miri)))]
    mod test {
        use super::*;
        use std::collections::BTreeSet;

        quickcheck::quickcheck! {
            fn take_parity(xs: Vec<usize>) -> bool {
                let odds = xs
                    .iter()
                    .cloned()
                    .filter(|x| x % 2 == 1)
                    .collect::<Vec<_>>();
                let mut avl_set = odds.iter().cloned().collect::<AvlTreeSet<_>>();
                let mut btree_set = odds.iter().cloned().collect::<BTreeSet<_>>();

                xs.iter().all( |x| avl_set.take(x) == btree_set.take(x))
            }
        }
    }
    #[cfg(all(test, miri))]
    mod test {
        use super::*;
        use quickcheck::{QuickCheck, TestResult};
        use std::cmp::max;
        use std::collections::BTreeSet;

        #[test]
        fn take_parity_test() {
            QuickCheck::new()
                .max_tests(3)
                // .min_tests_passed(3)
                .quickcheck(take_parity as fn(Vec<usize>) -> bool)
        }
        // quickcheck::quickcheck! {
        fn take_parity(xs: Vec<usize>) -> bool {
            let odds = xs
                .iter()
                .cloned()
                .filter(|x| x % 2 == 1)
                .collect::<Vec<_>>();
            let mut avl_set = odds.iter().cloned().collect::<AvlTreeSet<_>>();
            let mut btree_set = odds.iter().cloned().collect::<BTreeSet<_>>();

            xs.iter().all(|x| avl_set.take(x) == btree_set.take(x))
        }
        // }
    }
}
