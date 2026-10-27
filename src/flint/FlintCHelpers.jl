abstract type FlintStruct end

# unwrap singleton tuples, i.e. C's `foo_t x[1]` fields
@inline Base.getproperty(val::FlintStruct, name::Symbol) = _unwrap(getfield(val, name))
@inline _unwrap(v::Tuple{T}) where {T} = only(v)
@inline _unwrap(v) = v

# copy of `d` with field `name` replaced by `v`
function _setfield(d::T, name::Symbol, v) where {T<:FlintStruct}
  return T(ntuple(i -> fieldname(T, i) === name ? _wrap(fieldtype(T, i), v) : getfield(d, i), Val(fieldcount(T)))...)
end
_wrap(::Type{Tuple{T}}, v::Tuple{T}) where {T} = v
_wrap(::Type{Tuple{T}}, v) where {T} = (convert(T, v),)
_wrap(::Type, v) = v

"""
    _cstruct_type(::Type{T})

Return the type of the C struct behind `T`.

That is the type of the `cstruct` field, or `T` itself for a type without
one, such as a generated struct or `BigInt`.
"""
_cstruct_type(::Type{T}) where {T} = hasfield(T, :cstruct) ? fieldtype(T, :cstruct) : T

"""
    _cfield_path(::Type{T}, ::Val{name})

Return the C fields leading to property `name` of `T`, as a tuple of symbols.

That is `(name,)` for a C field, and the declared path for an extra or
legacy property defined by a plain field path; the macros define those
methods. The path is relative to [`_cstruct_type`](@ref)`(T)`.
"""
_cfield_path(::Type{T}, ::Val{name}) where {T, name} = (name,)

"""
    _path_offset(::Type{T}, path)
    _path_type(::Type{T}, path)

Return the byte offset and the type of the nested field `path` of the C
struct `T`, a tuple of symbols as returned by [`_cfield_path`](@ref).

A singleton array field is entered at its element.
"""
@inline function _path_offset(::Type{T}, path::Tuple{Symbol, Vararg{Symbol}}) where {T}
  i = Base.fieldindex(T, first(path))
  return fieldoffset(T, i) + _path_offset(_unwrap_type(fieldtype(T, i)), Base.tail(path))
end
@inline _path_offset(::Type, ::Tuple{}) = 0
@inline _path_type(::Type{T}, path::Tuple{Symbol, Vararg{Symbol}}) where {T} =
  _path_type(_unwrap_type(fieldtype(T, first(path))), Base.tail(path))
@inline _path_type(::Type{T}, ::Tuple{}) where {T} = T
_unwrap_type(::Type{Tuple{T}}) where {T} = T
_unwrap_type(::Type{T}) where {T} = T

# `@flint_fields T [f = JuliaType ...]` forwards `x.f` and `x.f = v` to the
# fields of `x.cstruct::FlintStruct`. A `f = JuliaType` pair converts that field
# on read, e.g. `entries = Ptr{ZZRingElem}` for Nemo's spelling of `fmpz*`.
macro flint_fields(T, block=:(begin end))
  @capture(block, begin conversions__ end) || error("expected a `begin` block, got `$block`")
  branches = map(conversions) do c
    @capture(c, f_ = ty_) || error("expected `field = Type`, got `$c`")
    :(s === $(QuoteNode(f)) && return $(esc(ty))(getfield(getfield(x, :cstruct), $(QuoteNode(f)))))
  end
  cfields = esc(Symbol("_", T, "_cfields"))
  jfields = esc(Symbol("_", T, "_jfields"))
  T = esc(T)
  # Julia fields win over C fields of the same name, so `x.cstruct` is always the
  # C struct. Extra and legacy properties win over C fields too, e.g. to keep
  # an enum field returning a `Cint` as before.
  return quote
    const $jfields = fieldnames($T)
    const $cfields = filter(!in($jfields), fieldnames(fieldtype($T, :cstruct)))
    @inline function Base.getproperty(x::$T, s::Symbol)
      s in $jfields && return getfield(x, s)
      $(branches...)
      (s in _extra_fieldnames($T) || s in _legacy_fieldnames($T)) && return _property(x, Val(s))
      s in $cfields && return getproperty(getfield(x, :cstruct), s)
      return getfield(x, s)
    end
    @inline function Base.setproperty!(x::$T, s::Symbol, v)
      s in $jfields && return setfield!(x, s, v)
      (s in _extra_fieldnames($T) || s in _legacy_fieldnames($T)) && return _set_property!(x, Val(s), v)
      s in $cfields && return setfield!(x, :cstruct, _setfield(getfield(x, :cstruct), s, v))
      return setfield!(x, s, v)
    end
    function Base.propertynames(x::$T, private::Bool=false)
      names = ($cfields..., _extra_fieldnames($T)..., filter(!=(:cstruct), $jfields)...)
      return private ? (names..., :cstruct, _legacy_fieldnames($T)...) : names
    end
  end
end

# Properties beyond the fields of `cstruct`, e.g. views into an opaque union.
# `@flint_extra_fields T name = expr ...` makes `x.name` evaluate `expr`, where
# `cstruct` is the C struct. A `begin` block may hold the pairs. The body must not
# go through `x.` again: inference gives up on that recursion.
#
# Writing `x.name = v` works when `expr` is a plain field path `cstruct.a.b`.
# Otherwise `name! = expr` gives the new C struct in terms of `cstruct` and `v`.
_extra_fieldnames(::Type) = ()
_set_property!(x, ::Val{s}, v) where {s} = error("property $s of $(typeof(x)) is read-only")

# Field names from before the generated structs, kept so that downstream code
# keeps working. To drop them, delete `@flint_legacy_fields` and its uses and
# `_legacy_fieldnames`.
_legacy_fieldnames(::Type) = ()

# `d` with the field at `path` replaced by `v`
@inline _setpath(d, path::Tuple{Symbol}, v) = _setfield(d, path[1], v)
@inline _setpath(d, path::Tuple, v) = _setfield(d, path[1], _setpath(getproperty(d, path[1]), Base.tail(path), v))

# word `i` of a union, and the union with word `i` replaced
@inline _union_word(d, i) = getfield(d, :uniondata)[i]
@inline _set_union_word(d, i, v) = _setfield(d, :uniondata, Base.setindex(getfield(d, :uniondata), _asword(v), i))
_asword(v::Ptr) = UInt(v)
_asword(v::Integer) = v % UInt

# `cstruct` in a property expression stands for the C struct
_subst_cstruct(ex) = postwalk(e -> e === :cstruct ? :(getfield(x, :cstruct)) : e, ex)

# `cstruct.a.b` as `(:a, :b)`, or nothing
function _field_path(ex)
  ex === :cstruct && return ()
  @capture(ex, inner_.field_) || return nothing
  path = _field_path(inner)
  return path === nothing ? nothing : (path..., field)
end

function _property_defs(T, block, namesfun)
  @capture(block, begin pairs__ end) || error("expected a `begin` block, got `$block`")
  defs = Expr[]
  names = Symbol[]
  setters = Base.Set{Symbol}()
  for c in pairs
    @capture(c, name_ = ex_) || error("expected `name = expr`, got `$c`")
    if endswith(string(name), "!")
      name = Symbol(chop(string(name)))
      push!(setters, name)
      push!(defs, :(@inline $(esc(:_set_property!))($(esc(:x))::$(esc(T)), ::Val{$(QuoteNode(name))}, $(esc(:v))) = setfield!($(esc(:x)), :cstruct, $(esc(_subst_cstruct(ex))))))
      continue
    end
    push!(names, name)
    push!(defs, :(@inline $(esc(:_property))($(esc(:x))::$(esc(T)), ::Val{$(QuoteNode(name))}) = $(esc(_subst_cstruct(ex)))))
    pth = _field_path(ex)
    # a conversion around a path, `Ptr{T}(cstruct.a.b)`, keeps the location
    cpth = pth !== nothing ? pth : @capture(ex, f_(inner_)) ? _field_path(inner) : nothing
    cpth === nothing || push!(defs, :($(esc(:_cfield_path))(::Type{$(esc(T))}, ::Val{$(QuoteNode(name))}) = $(Tuple(cpth))))
    if pth !== nothing && !isempty(pth) && !(name in setters)
      push!(setters, name)
      push!(defs, :(@inline $(esc(:_set_property!))($(esc(:x))::$(esc(T)), ::Val{$(QuoteNode(name))}, $(esc(:v))) = setfield!($(esc(:x)), :cstruct, _setpath(getfield($(esc(:x)), :cstruct), $(Tuple(pth)), $(esc(:v))))))
    end
  end
  push!(defs, :($(esc(namesfun))(::Type{$(esc(T))}) = $(Tuple(names))))
  return Expr(:block, defs...)
end

macro flint_extra_fields(T, block)
  return _property_defs(T, block, :_extra_fieldnames)
end

macro flint_legacy_fields(T, block)
  return _property_defs(T, block, :_legacy_fieldnames)
end
