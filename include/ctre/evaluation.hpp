#ifndef CTRE__EVALUATION__HPP
#define CTRE__EVALUATION__HPP

#include "flags_and_modes.hpp"
#include "atoms.hpp"
#include "atoms_unicode.hpp"
#include "starts_with_anchor.hpp"
#include "utility.hpp"
#include "return_type.hpp"
#include "find_captures.hpp"
#include "first.hpp"
#ifndef CTRE_IN_A_MODULE
#include <iterator>
#endif
#include <queue>

// remove me when MSVC fix the constexpr bug
#ifdef _MSC_VER
#ifndef CTRE_MSVC_GREEDY_WORKAROUND
#define CTRE_MSVC_GREEDY_WORKAROUND
#endif
#endif

namespace ctre {

template <size_t Limit> constexpr CTRE_FORCE_INLINE bool less_than_or_infinite([[maybe_unused]] size_t i) noexcept {
	if constexpr (Limit == 0) {
		// infinite
		return true;
	} else {
		return i < Limit;
	}
}

template <size_t Limit> constexpr CTRE_FORCE_INLINE bool less_than([[maybe_unused]] size_t i) noexcept {
	if constexpr (Limit == 0) {
		// infinite
		return false;
	} else {
		return i < Limit;
	}
}

constexpr bool is_bidirectional(const std::bidirectional_iterator_tag &) { return true; }
constexpr bool is_bidirectional(...) { return false; }

// sink for making the errors shorter
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator, Iterator, const EndIterator, flags, R, ...) noexcept {
	return false;
}

// if we found "accept" object on stack => ACCEPT
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator, Iterator, const EndIterator, flags, R captures, std::deque<R> & queue, ctll::list<accept>) noexcept {
	captures.success();
	return true;
}

// if we found "reject" object on stack => REJECT
template <typename R, typename... Rest, typename BeginIterator, typename Iterator, typename EndIterator> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator, Iterator, const EndIterator, flags, R, ctll::list<reject, Rest...>) noexcept {
	return false
}

// mark start of outer capture
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<start_mark, Tail...>) noexcept {
	return evaluate(begin, current, last, f, captures.set_start_mark(current), ctll::list<Tail...>());
}

// mark end of outer capture
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<end_mark, Tail...>) noexcept {
	return evaluate(begin, current, last, f, captures.set_end_mark(current), ctll::list<Tail...>());
}

// mark end of cycle
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator, Iterator current, const EndIterator, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, ctll::list<end_cycle_mark>) noexcept {
	if (cannot_be_empty_match(f)) {
		return false;
	}
	
	captures.set_end_mark(current);
	queue.push_back(captures);

	return true;
}

template<typename Head, typename... Tail>
struct is_iteration : is_iteration<Tail...> {};
template<> struct is_iteration<end_cycle_mark> : std::true_type{};
template<> struct is_iteration<end_mark, accept> : std::false_type{};


// matching everything which behave as a one character matcher
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename CharacterLike, typename... Tail, typename = std::enable_if_t<(MatchesCharacter<CharacterLike>::template value<decltype(*std::declval<Iterator>())>)>> 
constexpr /*CTRE_FORCE_INLINE*/ typename std::enable_if_t<!is_iteration<Tail...>::value, bool> evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<CharacterLike, Tail...>) noexcept {
	while (!captures.is_over_treshold()) {
		if(current == last) {
			if(captures.is_equal_treshold())
				return false;
			return evaluate(begin, current, last, consumed_something(f), captures.inc_delet(), queue, ctll::list<Tail...>());
		}

		if(CharacterLike::match_char(*current, f)) {
			return false;
		}

		auto subst_captures = captures;
		subst_captures.set_end_mark(current + 1);
		if(evaluate(begin, current + 1, last, consumed_something(f), subst_captures.inc_subst(), queue, ctll::list<Tail...>())) {
			return true;
		}

		auto delet_captures = captures;
		delet_captures.set_end_mark(current);
		if(evaluate(begin, current, last, consumed_something(f), subst_captures.inc_delet(), queue, ctll::list<Tail...>())) {
			return true;
		}

		auto & insrt_captures = captures;
		current++;
		insrt_captures.set_end_mark(current);
		insrt_captures.inc_insrt();
	}

	return false;	
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename CharacterLike, typename... Tail, typename = std::enable_if_t<(MatchesCharacter<CharacterLike>::template value<decltype(*std::declval<Iterator>())>)>> 
constexpr typename std::enable_if_t<is_iteration<Tail...>::value, bool> evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<CharacterLike, Tail...>) noexcept {
	auto result = false;

	while(!captures.is_over_treshold()){
		if(current == last){
			if(captures.is_equal_treshold())
				return false;
			return evaluate(begin, current, last, consumed_something(f), captures.inc_delet(), queue, ctll::list<Tail...>());
		}

		if(CharacterLike::match_char(*current, f)) {
			return evaluate(begin, ++current, last, consumed_something(f), captures, queue, ctll::list<Tail...>());
		}

		if(captures.is_equal_treshold()) {
			return true;
		}

		auto subst_captures = captures;
		subst_captures.set_end_mark(current + 1);
		result |= evaluate(begin, current + 1, last, consumed_something(f), subst_captures.inc_subst(), queue, ctll::list<Tail...>());

		auto delet_captures = captures;
		delet_captures.set_end_mark(current);
		result |= evaluate(begin, current, last, consumed_something(f), delet_captures.inc_subst(), queue, ctll::list<Tail...>());

		auto & insrt_captures = captures;
		current++;
		insrt_captures.set_end_mark(current);
		insrt_captures.inc_insrt();
	}

	return result;
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<any, Tail...>) noexcept {
	if (current == last) return false;
	
	if (multiline_mode(f)) {
		// TODO add support for different line ending and unicode (in a future unicode mode)
		if (*current == '\n') return false;
	}
	return evaluate(begin, ++current, last, consumed_something(f), captures, ctll::list<Tail...>());
}

// matching strings in patterns
/*
template <auto... String, typename Iterator, typename EndIterator> constexpr CTRE_FORCE_INLINE bool match_string([[maybe_unused]] Iterator & current, [[maybe_unused]] const EndIterator last, [[maybe_unused]] const flags & f) {
	return ((current != last && character<String>::match_char(*current++, f)) && ... && true);
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, auto... String, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, ctll::list<string<String...>, Tail...>) noexcept {
	if (!match_string<String...>(current, last, f)) {
		return not_matched;
	}

	return evaluate(begin, current, last, consumed_something(f, sizeof...(String) > 0), captures, ctll::list<Tail...>());
}
*/

// matching select in patterns
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename HeadOptions, typename... TailOptions, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<select<HeadOptions, TailOptions...>, Tail...>) noexcept {
	if (auto r = evaluate(begin, current, last, f, captures, ctll::list<HeadOptions, Tail...>())) {
		return r;
	} else {
		return evaluate(begin, current, last, f, captures, ctll::list<select<TailOptions...>, Tail...>());
	}
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator, Iterator, const EndIterator, flags, R, ctll::list<select<>, Tail...>) noexcept {
	// no previous option was matched => REJECT
	return false;
}

// matching sequence in patterns
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename HeadContent, typename... TailContent, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<sequence<HeadContent, TailContent...>, Tail...>) noexcept {
	if constexpr (sizeof...(TailContent) > 0) {
		return evaluate(begin, current, last, f, captures, ctll::list<HeadContent, sequence<TailContent...>, Tail...>());
	} else {
		return evaluate(begin, current, last, f, captures, ctll::list<HeadContent, Tail...>());
	}
}

// matching empty in patterns
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<empty, Tail...>) noexcept {
	return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
}

// matching asserts
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<assert_subject_begin, Tail...>) noexcept {
	if (begin != current) {
		return false;
	}
	return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<assert_subject_end, Tail...>) noexcept {
	if (last != current) {
		captures.add_insrt(last - current);
		if(!captures)
			return false;
	}
	return evaluate(begin, current, last, f, captures, queue, ctll::list<Tail...>());
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<assert_subject_end_line, Tail...>) noexcept {
	if (multiline_mode(f)) {
		if (last == current) {
			return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
		} else if (*current == '\n' && std::next(current) == last) {
			return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
		} else {
			return false;
		}
	} else {
		if (last != current) {
			captures.add_insrt(current - last);
			return captures.corrected();
		}
		return evaluate(begin, current, last, f, captures, queue, ctll::list<Tail...>());
	}
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<assert_line_begin, Tail...>) noexcept {
	if (multiline_mode(f)) {
		if (begin == current) {
			return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
		} else if (*std::prev(current) == '\n') {
			return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
		} else {
			return false;
		}
	} else {
		if (begin != current) {
			return false;
		}
		return evaluate(begin, current, last, f, captures, queue, ctll::list<Tail...>());
	}
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<assert_line_end, Tail...>) noexcept {
	if (multiline_mode(f)) {
		if (last == current) {
			return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
		} else if (*current == '\n') {
			return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
		} else {
			return false;
		}
	}
	
	// TODO properly match line end
	if (last != current) {
		return false;
	}
	return evaluate(begin, current, last, f, captures, queue, ctll::list<Tail...>());
}

// matching boundary
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename CharacterLike, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<boundary<CharacterLike>, Tail...>) noexcept {
	
	// reason why I need bidirectional iterators or some clever hack
	bool before = false;
	bool after = false;
	
	static_assert(is_bidirectional(typename std::iterator_traits<Iterator>::iterator_category{}), "To use boundary in regex you need to provide bidirectional iterator or range.");
	
	if (last != current) {
		after = CharacterLike::match_char(*current, f);
	}
	if (begin != current) {
		before = CharacterLike::match_char(*std::prev(current), f);
	}
	
	if (before == after) return false;
	
	return evaluate(begin, current, last, f, captures, queue, ctll::list<Tail...>());
}

// matching not_boundary
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename CharacterLike, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<not_boundary<CharacterLike>, Tail...>) noexcept {
	
	// reason why I need bidirectional iterators or some clever hack
	bool before = false;
	bool after = false;
	
	static_assert(is_bidirectional(typename std::iterator_traits<Iterator>::iterator_category{}), "To use boundary in regex you need to provide bidirectional iterator or range.");
	
	if (last != current) {
		after = CharacterLike::match_char(*current, f);
	}
	if (begin != current) {
		before = CharacterLike::match_char(*std::prev(current), f);
	}
	
	if (before != after) return false;
	
	return evaluate(begin, current, last, f, captures, queue, ctll::list<Tail...>());
}

// lazy repeat
/*
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, ctll::list<lazy_repeat<A,B,Content...>, Tail...>) noexcept {

	if constexpr (B != 0 && A > B) {
		return not_matched;
	} else {
		const Iterator backup_current = current;
	
		size_t i{0};
	
		while (less_than<A>(i)) {
			auto outer_result = evaluate(begin, current, last, not_empty_match(f), captures, ctll::list<Content..., end_cycle_mark>());
		
			if (!outer_result) return not_matched;
		
			captures = outer_result.unmatch();
			current = outer_result.get_end_position();
		
			++i;
		}
	
		if (auto outer_result = evaluate(begin, current, last, consumed_something(f, backup_current != current), captures, ctll::list<Tail...>())) {
			return outer_result;
		}
	
		while (less_than_or_infinite<B>(i)) {
			auto inner_result = evaluate(begin, current, last, not_empty_match(f), captures, ctll::list<Content..., end_cycle_mark>());
		
			if (!inner_result) return not_matched;
		
			auto outer_result = evaluate(begin, inner_result.get_end_position(), last, consumed_something(f), inner_result.unmatch(), ctll::list<Tail...>());
		
			if (outer_result) {
				return outer_result;
			}
		
			captures = inner_result.unmatch();
			current = inner_result.get_end_position();
		
			++i;
		}
	
		// rest of regex
		return evaluate(begin, current, last, consumed_something(f), captures, ctll::list<Tail...>());
	}
}
*/

// possessive repeat
/*
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, ctll::list<possessive_repeat<A,B,Content...>, Tail...>) noexcept {

	if constexpr ((B != 0) && (A > B)) {
		return not_matched;
	} else {
		const auto backup_current = current;

		for (size_t i{0}; less_than_or_infinite<B>(i); ++i) {
			// try as many of inner as possible and then try outer once
			auto inner_result = evaluate(begin, current, last, not_empty_match(f), captures, ctll::list<Content..., end_cycle_mark>());
		
			if (!inner_result) {
				if (!less_than<A>(i)) break;
				return not_matched;
			}
		
			captures = inner_result.unmatch();
			current = inner_result.get_end_position();
		}
	
		return evaluate(begin, current, last, consumed_something(f, backup_current != current), captures, ctll::list<Tail...>());
	}
}
*/

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr inline typename std::enable_if_t<((A == 0) && (B == 0)), bool> evaluate(size_t i, const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, ctll::list<repeat<A,B,Content...>, Tail...> stack) noexcept {
	captures.set_end_mark(current);
	queu.push_front(captures);
	R cptrs;

	while(!queue.empty()){
		cptrs = queue.front();
		queue.pop_front();

		if(auto tail_atmpt = cptrs; evaluate(begin, tail_atmpt.get_end_position(), last, f, tail_atmpt, queue, ctll::list<Tail...>()))
			return true;

		if(!evaluate(begin, cptrs.get_end_position(), last, f, cptrs, queue, ctll::list<Content..., end_cycle_mark>()))
			continue;
	}

	return false;
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE std::enable_if_t<((A == 1) && (B == 0)), bool> evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, [[maybe_unused]] ctll::list<repeat<A,B,Content...>, Tail...> stack) {
	captures.set_end_mark(current);
	return evaluate(begin, captures.get_end_position(), last, f, captures, queue, ctll::list<Content..., repeat<0,0,Content...>, Tail...>());
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE std::enable_if_t<((A > 1) && (B == 0)), bool> evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, [[maybe_unused]] ctll::list<repeat<A,B,Content...>, Tail...> stack) {
	captures.set_end_mark(current);
	return evaluate(begin, captures.get_end_position(), last, f, captures, queue, ctll::list<repeat<A,A,Content...>, repeat<0,0,Content...>, Tail...>());
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE std::enable_if_t<((A == 1) && (B == 1)), bool> evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, [[maybe_unused]] ctll::list<repeat<A,B,Content...>, Tail...> stack) {
	captures.set_end_mark(current);
	return evaluate(begin, captures.get_end_position(), last, f, captures, queue, ctll::list<Content..., Tail...>());
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE std::enable_if_t<((A == 0) && (B == 1)), bool> evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, [[maybe_unused]] ctll::list<repeat<A,B,Content...>, Tail...> stack) {
	captures.set_end_mark(current);
	return evaluate(begin, captures.get_end_position(), last, f, captures, queue, ctll::list<Tail...>()) ||
		   evaluate(begin, captures.get_end_position(), last, f, captures, queue, ctll::list<Content..., Tail...>());
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE std::enable_if_t<((A == 0) && (B > A) && (B != 1)), bool> evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, [[maybe_unused]] ctll::list<repeat<A,B,Content...>, Tail...> stack) {
	captures.set_end_mark(current);
	return evaluate(begin, captures.get_end_position(), last, f, captures, queue, ctll::list<repeat<B, B, Content...>, Tail...>()) ||
		   evaluate(begin, captures.get_end_position(), last, f, captures, queue, ctll::list<repeat<A, B - 1, Content...>, Tail...>());
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE std::enable_if_t<((A != 0) && (B > A)), bool> evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, [[maybe_unused]] ctll::list<repeat<A,B,Content...>, Tail...> stack) {
	captures.set_end_mark(current);
	return evaluate(begin, captures.get_end_position(), last, f, captures, queue, ctll::list<Content..., repeat<A - 1, B - 1, Content...>, Tail...>());
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t A, size_t B, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE std::enable_if_t<((A != 0) && (B == A) && (A != 1)), bool> evaluate(const BeginIterator begin, Iterator current, const EndIterator last, [[maybe_unused]] const flags & f, R captures, std::deque<R> & queue, [[maybe_unused]] ctll::list<repeat<A,B,Content...>, Tail...> stack) {
	captures.set_end_mark(current);
	return evaluate(begin, captures.get_end_position(), last, f, captures, queue, ctll::list<Content..., repeat<A - 1, B - 1, Content...>, Tail...>());
}

// capture (numeric ID)
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t Id, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<capture<Id, Content...>, Tail...>) noexcept {
	return evaluate(begin, current, last, f, captures.template start_capture<Id>(current), ctll::list<sequence<Content...>, numeric_mark<Id>, Tail...>());
}

// capture end mark (numeric and string ID)
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t Id, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<numeric_mark<Id>, Tail...>) noexcept {
	return evaluate(begin, current, last, f, captures.template end_capture<Id>(current), ctll::list<Tail...>());
}

// capture (string ID)
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, size_t Id, typename Name, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<capture_with_name<Id, Name, Content...>, Tail...>) noexcept {
	return evaluate(begin, current, last, f, captures.template start_capture<Id>(current), ctll::list<sequence<Content...>, numeric_mark<Id>, Tail...>());
}

// backreference support (match agains content of iterators)
template <typename Iterator> struct string_match {
	Iterator position;
	bool match;
};

template <typename Iterator, typename EndIterator> constexpr CTRE_FORCE_INLINE string_match<Iterator> match_against_range(Iterator current, const EndIterator last, Iterator range_current, const Iterator range_end, flags) noexcept {
	while (last != current && range_end != range_current) {
		if (*current == *range_current) {
			current++;
			range_current++;
		} else {
			return {current, false};
		}
	}
	return {current, range_current == range_end};
}

// backreference with name
template <typename R, typename Id, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<back_reference_with_name<Id>, Tail...>) noexcept {
	
	if (const auto ref = captures.template get<Id>()) {
		if (auto result = match_against_range(current, last, ref.begin(), ref.end(), f); result.match) {
			return evaluate(begin, result.position, last, consumed_something(f, ref.begin() != ref.end()), captures, ctll::list<Tail...>());
		}
	}
	return not_matched;
}

// backreference
template <typename R, size_t Id, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<back_reference<Id>, Tail...>) noexcept {
	
	if (const auto ref = captures.template get<Id>()) {
		if (auto result = match_against_range(current, last, ref.begin(), ref.end(), f); result.match) {
			return evaluate(begin, result.position, last, consumed_something(f, ref.begin() != ref.end()), captures, ctll::list<Tail...>());
		}
	}
	return not_matched;
}

// end of lookahead
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator, Iterator, const EndIterator, flags, R captures, std::deque<R> & queue, ctll::list<end_lookahead_mark>) noexcept {
	// TODO check interaction with non-empty flag
	return captures.matched();
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator, Iterator, const EndIterator, flags, R captures, std::deque<R> & queue, ctll::list<end_lookbehind_mark>) noexcept {
	// TODO check interaction with non-empty flag
	return captures.matched();
}

// lookahead positive
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<lookahead_positive<Content...>, Tail...>) noexcept {
	
	if (auto lookahead_result = evaluate(begin, current, last, f, captures, ctll::list<sequence<Content...>, end_lookahead_mark>())) {
		captures = lookahead_result.unmatch();
		return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
	} else {
		return not_matched;
	}
}

// lookahead negative
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<lookahead_negative<Content...>, Tail...>) noexcept {
	
	if (auto lookahead_result = evaluate(begin, current, last, f, captures, ctll::list<sequence<Content...>, end_lookahead_mark>())) {
		return not_matched;
	} else {
		return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
	}
}

// lookbehind positive
constexpr bool is_at_least_bidirectional(std::input_iterator_tag) {
	return false;
}

constexpr bool is_at_least_bidirectional(std::bidirectional_iterator_tag) {
	return true;
}

template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<lookbehind_positive<Content...>, Tail...>) noexcept {
	static_assert(is_at_least_bidirectional(typename std::iterator_traits<Iterator>::iterator_category{}), "to use lookbehind you must provide bi-directional iterator");
	
	if (auto lookbehind_result = evaluate(std::make_reverse_iterator(last), std::make_reverse_iterator(current), std::make_reverse_iterator(begin), f, captures, ctll::list<sequence<Content...>, end_lookbehind_mark>())) {
		captures = lookbehind_result.unmatch();
		return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
	} else {
		return not_matched;
	}
}

// lookbehind negative
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<lookbehind_negative<Content...>, Tail...>) noexcept {
	static_assert(is_at_least_bidirectional(typename std::iterator_traits<Iterator>::iterator_category{}), "to use negative lookbehind you must provide bi-directional iterator");
	
	if (auto lookbehind_result = evaluate(std::make_reverse_iterator(last), std::make_reverse_iterator(current), std::make_reverse_iterator(begin), f, captures, ctll::list<sequence<Content...>, end_lookbehind_mark>())) {
		return not_matched;
	} else {
		return evaluate(begin, current, last, f, captures, ctll::list<Tail...>());
	}
}

template <typename...> constexpr auto dependent_false = false;

// atomic_group<...> is just transformation to possessive_repeat<1,1,...>
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename... Content, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<atomic_group<Content...>, Tail...>) noexcept {
	return evaluate(begin, current, last, f, captures, ctll::list<possessive_repeat<1,1,Content...>, Tail...>{});
}

// switching modes
template <typename R, typename BeginIterator, typename Iterator, typename EndIterator, typename Mode, typename... Tail> 
constexpr CTRE_FORCE_INLINE auto evaluate(const BeginIterator begin, Iterator current, const EndIterator last, const flags & f, R captures, std::deque<R> & queue, ctll::list<mode_switch<Mode>, Tail...>) noexcept {
	return evaluate(begin, current, last, f + Mode{}, captures, ctll::list<Tail...>());
}


}

#endif
