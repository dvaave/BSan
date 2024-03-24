/*
 * See the dyninst/COPYRIGHT file for copyright information.
 * 
 * We provide the Paradyn Tools (below described as "Paradyn")
 * on an AS IS basis, and do not warrant its validity or performance.
 * We reserve the right to update, modify, or discontinue this
 * software at any time.  We shall have no obligation to supply such
 * updates or modifications or any other form of support to you.
 * 
 * By your use of Paradyn, you understand and agree that we (or any
 * other person or entity with proprietary rights in Paradyn) are
 * under no obligation to provide either maintenance services,
 * update services, notices of latent defects, or correction of
 * defects for Paradyn.
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */
#ifndef _LOCK_FREE_QUEUE_H_
#define _LOCK_FREE_QUEUE_H_

#include <iterator>
#include "race-detector-annotations.h"
#include <boost/atomic.hpp>

#define DEBUG_LOCKFREEQUEUE 0

#if DEBUG_LOCKFREEQUEUE
#define LFQ_DEBUG(x) x
#else
#define LFQ_DEBUG(x) 
#endif

template<typename T>
class LockFreeQueueItem {
private:
  typedef LockFreeQueueItem<T> item_type;

public:
  LockFreeQueueItem(T __value) : _next(0), _value(__value) {
    LFQ_DEBUG(validate = this); 
  };
  ~LockFreeQueueItem() { 
    LFQ_DEBUG(validate = 0); 
  };

  void setNext(item_type *__next) { 
    LFQ_DEBUG(assert(validate == this));
    race_detector_fake_lock_acquire(race_detector_fake_lock(_next));
    _next.store(__next); 
    race_detector_fake_lock_release(race_detector_fake_lock(_next));
  };

  void setNextPending() { 
    LFQ_DEBUG(assert(validate == this));
    race_detector_fake_lock_acquire(race_detector_fake_lock(_next));
    _next.store(pending()); 
    race_detector_fake_lock_release(race_detector_fake_lock(_next));
  };

  item_type *next() { 
    LFQ_DEBUG(assert(validate == this));
    race_detector_fake_lock_acquire(race_detector_fake_lock(_next));
    item_type *succ = _next.load();
    race_detector_fake_lock_release(race_detector_fake_lock(_next));
    // wait for successor to be written, if necessary
    while (succ == pending()) {
        race_detector_fake_lock_acquire(race_detector_fake_lock(_next));
        succ = _next.load();
        race_detector_fake_lock_release(race_detector_fake_lock(_next));
    }
    return succ;
  };

  T value() { 
    LFQ_DEBUG(assert(validate == this));
    return _value; 
  };

private:
  item_type *pending() { 
    LFQ_DEBUG(assert(validate == this));
    return (item_type * const) ~0; 
  }

  boost::atomic<item_type *> _next;
  T _value;
  LFQ_DEBUG(item_type *validate);
};


// designed for use in a context where where only insert_chain operations
// that have completed their exchange may be concurrent with iteration on
// the queue
template<typename T>
class LockFreeQueueIterator {
private:
  typedef LockFreeQueueItem<T> item_type;
  typedef LockFreeQueueIterator<T> iterator;

public:
  typedef T value_type;
  typedef T * pointer;
  typedef T & reference;
  typedef std::ptrdiff_t difference_type;
  typedef std::forward_iterator_tag iterator_category;

public:
  LockFreeQueueIterator(item_type *_item) : item(_item) {};

  T operator *() { return item->value(); };

  bool operator != (iterator i) { return item != i.item; };

  iterator operator ++() { 
    if (item) item = item->next(); 
    return *this; 
  };

  iterator operator ++(int) { 
    iterator clone(*this);
    ++(*this);
    return clone;
  };

private:
  item_type *item;
};


template<typename T>
class LockFreeQueue {
public:
  typedef LockFreeQueueIterator<T> iterator;
  typedef LockFreeQueueItem<T> item_type; 

public:
  LockFreeQueue(item_type *_head = 0) : head(_head) {};

public: 
  // wait-free member functions designed for concurrent use

  // insert a singleton at the head of the queue
  // note: this operation is wait-free unless the allocator blocks 
  void insert(T value) {
    item_type *entry = new item_type(value);
    insert_chain(entry, entry);
  };

  // steal the linked list from q and insert it at the front of this queue
  void splice(LockFreeQueue<T> &q) {
    if (q.peek()) { // only empty q if it is non-empty 
      item_type *first = q.steal();
      item_type *last = first;
      for (;;) {
	item_type *next = last->next();
	if (!next) break;
	last = next;
      }
      insert_chain(first, last);
    }
  };

  // inspect the head of the queue
  item_type *peek() { 
      race_detector_fake_lock_acquire(race_detector_fake_lock(head));
      item_type* ret = head.load();
      race_detector_fake_lock_release(race_detector_fake_lock(head));
      return ret; 
  };

  // grab the contents of the queue for your own private use
  item_type *steal() { 
      race_detector_fake_lock_acquire(race_detector_fake_lock(head));
      item_type* ret = head.exchange(0);
      race_detector_fake_lock_release(race_detector_fake_lock(head));
      return ret; 
  };

public:
  // designed for use in a context where where only insert_chain 
  // operations that have completed their exchange may be concurrent

  item_type *pop() { 
    race_detector_fake_lock_acquire(race_detector_fake_lock(head));
    item_type *first = head.load();
    race_detector_fake_lock_release(race_detector_fake_lock(head));
    if (first) {
      item_type *succ = first->next(); 
      race_detector_fake_lock_acquire(race_detector_fake_lock(head));
      head.store(succ);
      race_detector_fake_lock_release(race_detector_fake_lock(head));
      first->setNext(0);
    }
    return first;
  };

  iterator begin() { 
      race_detector_fake_lock_acquire(race_detector_fake_lock(head));
      iterator ret(head.load());
      race_detector_fake_lock_release(race_detector_fake_lock(head));     
      return ret; 
  };

  iterator end() { return iterator(0); };

  ~LockFreeQueue() { clear(); };

  void clear() { 
    item_type *first;
    while((first = pop())) { 
      delete first;
    }
  };

private:

  // insert a chain at the head of the queue
  void insert_chain(item_type *first, item_type *last) { 
    last->setNextPending(); // make in-progress splice visible
    race_detector_fake_lock_acquire(race_detector_fake_lock(head));
    item_type *oldhead = head.exchange(first);
    race_detector_fake_lock_release(race_detector_fake_lock(head));     
    last->setNext(oldhead);
  };

private:
  boost::atomic<item_type *> head;
};

#endif
