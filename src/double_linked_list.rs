use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::mem::{replace, swap, transmute};
use std::rc::{Rc, Weak};

/// 双链表
pub struct LinkedList<T> {
    head: Option<Rc<RefCell<Node<T>>>>,
    tail: Weak<RefCell<Node<T>>>,
    len: usize,
}

/// 链表节点
struct Node<T> {
    next: Option<Rc<RefCell<Node<T>>>>,
    prev: Weak<RefCell<Node<T>>>,
    elem: T,
}

/// 链表迭代器
pub struct Iter<'a, T> {
    start: Option<Rc<RefCell<Node<T>>>>,
    end: Weak<RefCell<Node<T>>>,
    list: &'a LinkedList<T>,
}

/// 链表可变迭代器
pub struct IterMut<'a, T> {
    start: Option<Rc<RefCell<Node<T>>>>,
    end: Weak<RefCell<Node<T>>>,
    list: &'a LinkedList<T>,
}

impl<T> LinkedList<T> {
    /// 创建一个空链表
    pub fn new() -> Self {
        Self {
            head: None,
            tail: Weak::new(),
            len: 0,
        }
    }

    /// 将元素插入到链表头部
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// list.push_front(1);
    /// assert_eq!(list.front(), Some(&1));
    /// ```
    pub fn push_front(&mut self, elem: T) {
        self.len += 1;
        let new_node = Rc::new(RefCell::new(Node {
            next: self.head.clone(),
            prev: Weak::new(),
            elem,
        }));

        match &self.head {
            Some(h) => {
                h.borrow_mut().prev = Rc::downgrade(&new_node);
            }
            None => {
                self.tail = Rc::downgrade(&new_node);
            }
        }

        self.head = Some(new_node);
    }

    /// 将元素插入到链表尾部
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// list.push_back(1);
    /// assert_eq!(list.back(), Some(&1));
    /// ```
    pub fn push_back(&mut self, elem: T) {
        match self.tail.upgrade() {
            Some(tail) => {
                self.len += 1;
                let node = Rc::new(RefCell::new(Node {
                    next: None,
                    prev: Rc::downgrade(&tail),
                    elem,
                }));
                self.tail = Rc::downgrade(&node);
                tail.borrow_mut().next = Some(node);
            }
            None => self.push_front(elem),
        }
    }

    /// 将第一个元素返回
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// list.push_front(1);
    /// assert_eq!(list.pop_front(), Some(1));
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|h| {
            self.len -= 1;
            let h = Rc::try_unwrap(h)
                .ok()
                .expect("this should be the last ref")
                .into_inner();
            self.head = h.next;
            h.elem
        })
    }

    /// 将最后一个元素返回
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// list.push_back(1);
    /// assert_eq!(list.pop_back(), Some(1));
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.upgrade().map(|t| {
            self.len -= 1;
            // drop strong ref, so we could call `Rc::try_unwrap`.
            match t.borrow().prev.upgrade() {
                Some(x) => x.borrow_mut().next = None,
                None => self.head = None,
            }
            let t = Rc::try_unwrap(t)
                .ok()
                .expect("this should be the last ref")
                .into_inner();
            self.tail = t.prev;
            t.elem
        })
    }

    /// 返回链表第一个元素的引用  
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.front(), None);
    /// list.push_front(1);
    /// assert_eq!(list.front(), Some(&1));
    /// ```
    pub fn front(&self) -> Option<&T> {
        // return type has no guard, unsafe in inevitable.
        // SAFETY: the lifetime of `&T` is bounded to `&self`, so it's immutable.
        self.head
            .as_ref()
            .and_then(|x| unsafe { transmute(&x.borrow().elem) })
    }

    /// 返回链表第一个元素的可变引用   
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.head
            .as_ref()
            .and_then(|x| unsafe { transmute(&x.borrow_mut().elem) })
    }

    /// 返回链表最后一个元素的引用
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.back(), None);
    /// list.push_back(1);
    /// assert_eq!(list.back(), Some(&1));
    /// ```
    pub fn back(&self) -> Option<&T> {
        self.tail
            .upgrade()
            .and_then(|x| unsafe { transmute(&x.borrow().elem) })
    }

    /// 返回链表最后一个元素的可变引用
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.tail
            .upgrade()
            .and_then(|x| unsafe { transmute(&x.borrow_mut().elem) })
    }

    /// 返回链表长度
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// list.push_back(1);
    /// assert_eq!(list.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// 判断链表是否为空
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 清空链表
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// list.push_back(1);
    /// list.push_back(2);
    /// assert_eq!(list.len(), 2);
    /// list.clear();
    /// assert_eq!(list.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        // Oh look it's drop again
        while self.pop_front().is_some() {}
    }

    /// 返回一个迭代器
    pub fn iter(&self) -> Iter<T> {
        Iter {
            start: self.head.clone(),
            end: self.tail.clone(),
            list: self,
        }
    }

    /// 返回一个可变迭代器
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            start: self.head.clone(),
            end: self.tail.clone(),
            list: self,
        }
    }

    fn get_raw(&self, at: usize) -> Option<Rc<RefCell<Node<T>>>> {
        let mut cur = self.head.clone()?;
        for _ in 0..at {
            let next = cur.borrow().next.clone()?;
            cur = next;
        }
        Some(cur)
    }

    /// 获取链表中指定位置的元素   
    /// 如果超出范围，使用panic!宏抛出异常
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// list.push_back(1);
    /// assert_eq!(list.get(0), &1);
    /// ```
    pub fn get(&self, at: usize) -> &T {
        let cur = self
            .get_raw(at)
            .expect("don't think we should panic, but will do");
        let inner = cur.borrow();
        unsafe { transmute(&inner.elem) }
    }

    /// 获取链表中指定位置的可变元素
    pub fn get_mut(&mut self, at: usize) -> &mut T {
        let cur = self
            .get_raw(at)
            .expect("don't think we should panic, but will do");
        let mut inner = cur.borrow_mut();
        unsafe { transmute(&mut inner.elem) }
    }

    /// 将元素插入到**下标为i**的位置    
    /// 如果超出范围，使用panic!宏抛出异常
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// list.insert(0,1);
    /// list.insert(1,3);
    /// list.insert(1,2);
    /// assert_eq!(list.get(0), &1);
    /// assert_eq!(list.get(1), &2);
    /// assert_eq!(list.get(2), &3);
    /// ```
    pub fn insert(&mut self, at: usize, data: T) {
        // check here, so we don't need to worry about boundries later
        if at == 0 {
            return self.push_front(data);
        }
        if at == self.len {
            return self.push_back(data);
        }

        self.len += 1;

        let cur = self
            .get_raw(at)
            .expect("don't think we should panic, but will do");

        let mut inner = cur.borrow_mut();

        // set new
        let new_node = Rc::new(RefCell::new(Node {
            next: Some(cur.clone()),
            prev: inner.prev.clone(),
            elem: data,
        }));

        // set next
        let prev = replace(&mut inner.prev, Rc::downgrade(&new_node));

        // set prev
        if let Some(prev) = prev.upgrade() {
            prev.borrow_mut().next = Some(new_node)
        }
    }

    /// 移除链表中下标为i的元素
    /// 如果超出范围，使用panic!宏抛出异常
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::from_iter(vec![1,2,3]);
    /// assert_eq!(list.remove(1), 2);
    pub fn remove(&mut self, at: usize) -> T {
        if at == 0 {
            return self
                .pop_front()
                .expect("don't think we should panic, but will do");
        }
        if at == self.len {
            return self
                .pop_back()
                .expect("don't think we should panic, but will do");
        }
        self.len -= 1;

        let cur = self
            .get_raw(at)
            .expect("don't think we should panic, but will do");

        let inner = cur.borrow();

        // set prev, also drop prev ref
        if let Some(prev) = inner.prev.upgrade() {
            prev.borrow_mut().next = inner.next.clone()
        }

        // destroy cur
        drop(inner);
        let inner = Rc::try_unwrap(cur)
            .ok()
            .expect("this should be the last ref")
            .into_inner();

        // set next
        if let Some(next) = inner.next {
            next.borrow_mut().prev = inner.prev;
        }

        inner.elem
    }

    /// 将链表分割成两个链表，原链表为[0,at-1]，新链表为[at,len-1]。
    /// 如果超出范围，使用panic!宏抛出异常
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::from_iter(vec![1,2,3,4,5]);
    /// let new = list.split_off(2); // list = [1,2], new = [3,4,5]
    /// assert_eq!(list.len(), 2);
    /// assert_eq!(list.pop_front(), Some(1));
    /// assert_eq!(list.pop_front(), Some(2));
    pub fn split_off(&mut self, at: usize) -> LinkedList<T> {
        if at == 0 {
            return replace(self, LinkedList::new());
        }
        if at == self.len {
            return LinkedList::new();
        }

        let cur = self
            .get_raw(at)
            .expect("don't think we should panic, but will do");

        // tmp for later use
        let old_len = self.len;
        let old_tail = self.tail.clone();

        // set fields for self
        self.len = at;
        let mut inner = cur.borrow_mut();
        inner
            .prev
            .upgrade()
            .expect("this one must exist, we checked before")
            .borrow_mut()
            .next = None;
        self.tail = inner.prev.clone();

        // set fields for new
        inner.prev = Weak::new();
        drop(inner);
        LinkedList {
            head: Some(cur),
            tail: old_tail,
            len: old_len - at,
        }
    }

    /// 查找链表中第一个满足条件的元素
    ///
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::from_iter(vec![1,2,3]);
    /// assert_eq!(list.find_mut(|x| x % 2 == 0), Some(&mut 2));
    /// assert_eq!(list.find_mut(|x| x % 4 == 0), None);
    /// ```
    pub fn find_mut<P>(&mut self, predicate: P) -> Option<&mut T>
    where
        P: Fn(&T) -> bool,
    {
        for elem in self {
            if predicate(elem) {
                return Some(unsafe { transmute(elem) });
            }
        }
        None
    }
}

impl<T: PartialEq> LinkedList<T> {
    /// 判断链表中是否包含某个元素
    ///
    /// # Examples
    /// ```
    /// use linked_list::double_linked_list::LinkedList;
    /// let mut list = LinkedList::new();
    /// list.push_back(1);
    /// assert_eq!(list.contains(&1), true);
    /// assert_eq!(list.contains(&2), false);
    /// ```
    pub fn contains(&mut self, data: &T) -> bool {
        self.iter().any(|x| x == data)
    }
}

impl<'a, T> IntoIterator for &'a LinkedList<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut LinkedList<T> {
    type IntoIter = IterMut<'a, T>;
    type Item = &'a mut T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    // 返回下一个元素，当没有元素可返回时，返回None
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.start.as_ref().and_then(|x| x.borrow().next.clone());
        let cur = replace(&mut self.start, next);
        cur.as_ref().map(|x| unsafe { transmute(&x.borrow().elem) })
    }

    // 返回(self.len, Some(self.len))即可
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}
impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.start.as_ref().and_then(|x| x.borrow().next.clone());
        let cur = replace(&mut self.start, next);
        cur.as_ref()
            .map(|x| unsafe { transmute(&mut x.borrow_mut().elem) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    // 返回前一个元素
    fn next_back(&mut self) -> Option<Self::Item> {
        let cur = self.end.upgrade();
        let prev = match &cur {
            Some(x) => x.borrow().prev.clone(),
            None => Weak::new(),
        };
        self.end = prev;
        cur.as_ref().map(|x| unsafe { transmute(&x.borrow().elem) })
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let cur = self.end.upgrade();
        let prev = match &cur {
            Some(x) => x.borrow().prev.clone(),
            None => Weak::new(),
        };
        self.end = prev;
        cur.as_ref()
            .map(|x| unsafe { transmute(&mut x.borrow_mut().elem) })
    }
}

/// 提供归并排序的功能
pub trait MergeSort {
    /// 就地进行归并排序，按从小到大排序
    fn merge_sort(&mut self);
}

impl<T: PartialOrd + Default> LinkedList<T> {
    fn pop_front_raw(&mut self) -> Option<Rc<RefCell<Node<T>>>> {
        self.len -= 1;
        // clear value & set head
        let cur = self.head.take();
        self.head = cur.as_ref().and_then(|x| {
            let mut x = x.borrow_mut();
            x.prev = Weak::new();
            x.next.take()
        });

        // clear head
        if let Some(head) = &self.head {
            head.borrow_mut().prev = Weak::new()
        }

        cur
    }

    fn push_back_raw(&mut self, raw: Rc<RefCell<Node<T>>>) {
        self.len += 1;
        // set value
        let mut inner = raw.borrow_mut();
        inner.next = None;
        inner.prev = self.tail.clone();
        drop(inner);

        match self.tail.upgrade() {
            Some(t) => t.borrow_mut().next = Some(raw.clone()),
            None => self.head = Some(raw.clone()),
        }
        self.tail = Rc::downgrade(&raw);
    }
}

impl<T: PartialOrd + Default> MergeSort for LinkedList<T> {
    fn merge_sort(&mut self) {
        match self.len {
            0 | 1 => return,
            2 => {
                let first = self.head.clone().expect("we got this");
                let mut first = first.borrow_mut();
                let second = first.next.clone().expect("we got this");
                let mut second = second.borrow_mut();
                if first.elem > second.elem {
                    swap(&mut first.elem, &mut second.elem)
                }
            }
            _ => {
                let mid = self.len / 2;
                let mut left = replace(self, LinkedList::new());
                let mut right = left.split_off(mid);

                left.merge_sort();
                right.merge_sort();

                loop {
                    let lv = left.front();
                    let rv = right.front();
                    match (lv, rv) {
                        (Some(l), Some(r)) => {
                            if l < r {
                                self.push_back_raw(left.pop_front_raw().unwrap())
                            } else {
                                self.push_back_raw(right.pop_front_raw().unwrap())
                            }
                        }
                        (Some(_), None) => self.push_back_raw(left.pop_front_raw().unwrap()),
                        (None, Some(_)) => self.push_back_raw(right.pop_front_raw().unwrap()),
                        (None, None) => break,
                    }
                }
            }
        }
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        // Pop until we have to stop
        while self.pop_front().is_some() {}
    }
}

impl<T> Default for LinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Clone for LinkedList<T> {
    fn clone(&self) -> Self {
        let mut new_list = Self::new();
        for item in self {
            new_list.push_back(item.clone());
        }
        new_list
    }
}
impl<T> Extend<T> for LinkedList<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push_back(item);
        }
    }
}
impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        list.extend(iter);
        list
    }
}

impl<T: Debug> Debug for LinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq> PartialEq for LinkedList<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }
}

impl<T: Eq> Eq for LinkedList<T> {}

impl<T: PartialOrd> PartialOrd for LinkedList<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for LinkedList<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T: Hash> Hash for LinkedList<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for item in self {
            item.hash(state);
        }
    }
}

unsafe impl<T: Send> Send for LinkedList<T> {}
unsafe impl<T: Sync> Sync for LinkedList<T> {}

unsafe impl<'a, T: Send> Send for Iter<'a, T> {}
unsafe impl<'a, T: Sync> Sync for Iter<'a, T> {}

unsafe impl<'a, T: Send> Send for IterMut<'a, T> {}
unsafe impl<'a, T: Sync> Sync for IterMut<'a, T> {}
