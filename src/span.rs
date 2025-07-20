/*
 * Copyright 2018-2024 Felix Garcia Carballeira, Alejandro Calderon Mateos, Diego Camarmas Alonso,
 * Álvaro Guerrero Espinosa
 *
 * This file is part of CREATOR.
 *
 * CREATOR is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * CREATOR is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with CREATOR.  If not, see <http://www.gnu.org/licenses/>.
 */

//! Module containing the definition of the spans used to track regions of the assembly source code
//! throughout the crate

/// Range of characters in the source code of an element
pub type Span = chumsky::span::SimpleSpan<usize>;
/// Value with an attached [`Span`]
pub type Spanned<T> = (T, Span);

/// Dynamically generated source code for a [`Span`]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Source {
    /// Source assembly code
    pub code: String,
    /// Span of this dynamically generated code
    pub span: SpanList,
}

/// [`Span`] that carries its source code, used to point into dynamically generated source code
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpanList {
    /// [`Span`] of the element in its source code
    pub span: Span,
    /// Source of the element, [`None`] if it comes from the user's assembly source code
    pub source: Option<std::rc::Rc<Source>>,
}

impl From<Span> for SpanList {
    fn from(span: Span) -> Self {
        Self { span, source: None }
    }
}

impl From<&Span> for SpanList {
    fn from(span: &Span) -> Self {
        (*span).into()
    }
}

type Range = std::ops::Range<usize>;

impl From<Range> for SpanList {
    fn from(span: Range) -> Self {
        Span::from(span).into()
    }
}

impl From<(Span, &Self)> for SpanList {
    fn from(value: (Span, &Self)) -> Self {
        Self {
            span: value.0,
            source: value.1.source.clone(),
        }
    }
}
