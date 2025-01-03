################################################################################
#
#  fq_default_mat.jl: flint fq_default_mat types in julia
#
################################################################################

################################################################################
#
#  Data type and parent object methods
#
################################################################################

dense_matrix_type(::Type{FqFieldElem}) = FqMatrix

###############################################################################
#
#   Similar & zero
#
###############################################################################

similar(::FqMatrix, R::FqField, r::Int, c::Int) = FqMatrix(r, c, R)
zero(m::FqMatrix, R::FqField, r::Int, c::Int) = FqMatrix(r, c, R)

################################################################################
#
#  Manipulation
#
################################################################################

function getindex!(v::FqFieldElem, a::FqMatrix, i::Int, j::Int)
  @boundscheck _checkbounds(a, i, j)
  ccall((:fq_default_mat_entry, libflint), Ptr{FqFieldElem},
        (Ref{FqFieldElem}, Ref{FqMatrix}, Int, Int, Ref{FqField}),
        v, a, i - 1 , j - 1, base_ring(a))
  return v
end

@inline function getindex(a::FqMatrix, i::Int, j::Int)
  @boundscheck _checkbounds(a, i, j)
  z = base_ring(a)()
  ccall((:fq_default_mat_entry, libflint), Ptr{FqFieldElem},
        (Ref{FqFieldElem}, Ref{FqMatrix}, Int, Int,
         Ref{FqField}),
        z, a, i - 1 , j - 1, base_ring(a))
  return z
end

@inline function setindex!(a::FqMatrix, u::FqFieldElemOrPtr, i::Int, j::Int)
  @boundscheck _checkbounds(a, i, j)
  uu = base_ring(a)(u)
  @ccall libflint.fq_default_mat_entry_set(
    a::Ref{FqMatrix}, (i-1)::Int, (j-1)::Int, uu::Ref{FqFieldElem}, base_ring(a)::Ref{FqField}
  )::Nothing
end

@inline function setindex!(a::FqMatrix, u::ZZRingElem, i::Int, j::Int)
  @boundscheck _checkbounds(a, i, j)
  ccall((:fq_default_mat_entry_set_fmpz, libflint), Nothing,
        (Ref{FqMatrix}, Int, Int, Ref{ZZRingElem},
         Ref{FqField}),
        a, i - 1, j - 1, u, base_ring(a))
  nothing
end

setindex!(a::FqMatrix, u::Integer, i::Int, j::Int) = setindex!(a, base_ring(a)(u), i, j)

function setindex!(a::FqMatrix, b::FqMatrix, r::UnitRange{Int64}, c::UnitRange{Int64})
  _checkbounds(a, r, c)
  size(b) == (length(r), length(c)) || throw(DimensionMismatch("tried to assign a $(size(b, 1))x$(size(b, 2)) matrix to a $(length(r))x$(length(c)) destination"))
  A = view(a, r, c)
  ccall((:fq_default_mat_set, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), A, b, base_ring(a))
end

function deepcopy_internal(a::FqMatrix, dict::IdDict)
  z = FqMatrix(nrows(a), ncols(a), base_ring(a))
  ccall((:fq_default_mat_set, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), z, a, base_ring(a))
  return z
end

function number_of_rows(a::FqMatrix)
  return ccall((:fq_default_mat_nrows, libflint), Int,
               (Ref{FqMatrix}, Ref{FqField}),
               a, base_ring(a))
end

function number_of_columns(a::FqMatrix)
  return ccall((:fq_default_mat_ncols, libflint), Int,
               (Ref{FqMatrix}, Ref{FqField}),
               a, base_ring(a))
end

base_ring(a::FqMatrix) = a.base_ring

function one(a::FqMatrixSpace)
  (nrows(a) != ncols(a)) && error("Matrices must be square")
  return a(one(base_ring(a)))
end

function iszero(a::FqMatrix)
  r = ccall((:fq_default_mat_is_zero, libflint), Cint,
            (Ref{FqMatrix}, Ref{FqField}), a, base_ring(a))
  return Bool(r)
end

@inline function is_zero_entry(A::FqMatrix, i::Int, j::Int)
  @boundscheck _checkbounds(A, i, j)
  GC.@preserve A begin
    x = fq_default_mat_entry_ptr(A, i, j)
    return ccall((:fq_default_is_zero, libflint), Bool,
                 (Ptr{FqFieldElem}, Ref{FqField}), x, base_ring(A))
  end
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(a::FqMatrix, b::FqMatrix)
  if !(a.base_ring == b.base_ring)
    return false
  end
  r = ccall((:fq_default_mat_equal, libflint), Cint,
            (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), a, b, base_ring(a))
  return Bool(r)
end

isequal(a::FqMatrix, b::FqMatrix) = ==(a, b)

################################################################################
#
#  Transpose
#
################################################################################

function transpose(a::FqMatrix)
  z = similar(a, ncols(a), nrows(a))
  if _fq_default_ctx_type(base_ring(a)) == _FQ_DEFAULT_NMOD
    ccall((:nmod_mat_transpose, libflint), Nothing, (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), z, a, base_ring(a))
    return z
  elseif _fq_default_ctx_type(base_ring(a)) == _FQ_DEFAULT_FMPZ_NMOD
    ccall((:fmpz_mod_mat_transpose, libflint), Nothing, (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), z, a, base_ring(a))
    return z
  end
  # There is no flint functionality for the other cases
  t = base_ring(a)()
  for i in 1:nrows(a)
    for j in 1:ncols(a)
      getindex!(t, a, i, j)
      z[j, i] = t
    end
  end
  return z
end

###############################################################################
#
#   Row and column swapping
#
###############################################################################

function swap_rows!(x::FqMatrix, i::Int, j::Int)
  ccall((:fq_default_mat_swap_rows, libflint), Nothing,
        (Ref{FqMatrix}, Ptr{Nothing}, Int, Int, Ref{FqField}),
        x, C_NULL, i - 1, j - 1, base_ring(x))
  return x
end

function swap_rows(x::FqMatrix, i::Int, j::Int)
  (1 <= i <= nrows(x) && 1 <= j <= nrows(x)) || throw(BoundsError())
  y = deepcopy(x)
  return swap_rows!(y, i, j)
end

function swap_cols!(x::FqMatrix, i::Int, j::Int)
  ccall((:fq_default_mat_swap_cols, libflint), Nothing,
        (Ref{FqMatrix}, Ptr{Nothing}, Int, Int, Ref{FqField}),
        x, C_NULL, i - 1, j - 1, base_ring(x))
  return x
end

function swap_cols(x::FqMatrix, i::Int, j::Int)
  (1 <= i <= ncols(x) && 1 <= j <= ncols(x)) || throw(BoundsError())
  y = deepcopy(x)
  return swap_cols!(y, i, j)
end

function reverse_rows!(x::FqMatrix)
  ccall((:fq_default_mat_invert_rows, libflint), Nothing,
        (Ref{FqMatrix}, Ptr{Nothing}, Ref{FqField}), x, C_NULL, base_ring(x))
  return x
end

reverse_rows(x::FqMatrix) = reverse_rows!(deepcopy(x))

function reverse_cols!(x::FqMatrix)
  ccall((:fq_default_mat_invert_cols, libflint), Nothing,
        (Ref{FqMatrix}, Ptr{Nothing}, Ref{FqField}), x, C_NULL, base_ring(x))
  return x
end

reverse_cols(x::FqMatrix) = reverse_cols!(deepcopy(x))

################################################################################
#
#  Unary operators
#
################################################################################

-(x::FqMatrix) = neg!(similar(x), x)

################################################################################
#
#  Binary operators
#
################################################################################

function +(x::FqMatrix, y::FqMatrix)
  check_parent(x,y)
  z = similar(x)
  ccall((:fq_default_mat_add, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}),
        z, x, y, base_ring(x))
  return z
end

function -(x::FqMatrix, y::FqMatrix)
  check_parent(x,y)
  z = similar(x)
  ccall((:fq_default_mat_sub, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}),
        z, x, y, base_ring(x))

  return z
end

function *(x::FqMatrix, y::FqMatrix)
  (base_ring(x) != base_ring(y)) && error("Base ring must be equal")
  (ncols(x) != nrows(y)) && error("Dimensions are wrong")
  z = similar(x, nrows(x), ncols(y))
  ccall((:fq_default_mat_mul, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), z, x, y, base_ring(x))
  return z
end


################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::FqMatrix)
  ccall((:fq_default_mat_zero, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqField}), a, base_ring(a))
  return a
end

function one!(a::FqMatrix)
  ccall((:fq_default_mat_one, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqField}), a, base_ring(a))
  return a
end

function neg!(z::FqMatrix, a::FqMatrix)
  ccall((:fq_default_mat_neg, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), z, a, base_ring(a))
  return z
end

function mul!(a::FqMatrix, b::FqMatrix, c::FqMatrix)
  ccall((:fq_default_mat_mul, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}),
        a, b, c, base_ring(a))
  return a
end

function mul!(a::FqMatrix, b::FqMatrix, c::FqFieldElem)
  F = base_ring(a)
  if _fq_default_ctx_type(F) == _FQ_DEFAULT_NMOD
    ccall((:nmod_mat_scalar_mul, libflint), Nothing, (Ref{FqMatrix}, Ref{FqMatrix}, UInt), a, b, UInt(lift(ZZ, c)))
    return a
  end
  GC.@preserve a begin
    for i in 1:nrows(a)
      for j in 1:ncols(a)
        x = fq_default_mat_entry_ptr(a, i, j)
        y = fq_default_mat_entry_ptr(b, i, j)
        ccall((:fq_default_mul, libflint), Nothing, (Ptr{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqFieldElem}, Ref{FqField}), x, y, c, F)
      end
    end
  end
  return a
end

mul!(a::FqMatrix, b::FqFieldElem, c::FqMatrix) = mul!(a, c, b)

function add!(a::FqMatrix, b::FqMatrix, c::FqMatrix)
  ccall((:fq_default_mat_add, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}),
        a, b, c, base_ring(a))
  return a
end

function Generic.add_one!(a::FqMatrix, i::Int, j::Int)
  @boundscheck _checkbounds(a, i, j)
  F = base_ring(a)
  GC.@preserve a begin
    x = fq_default_mat_entry_ptr(a, i, j)
    # There is no fq_default_add_one, but only ...sub_one
    ccall((:fq_default_neg, libflint), Nothing,
          (Ptr{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqField}),
          x, x, F)
    ccall((:fq_default_sub_one, libflint), Nothing,
          (Ptr{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqField}),
          x, x, F)
    ccall((:fq_default_neg, libflint), Nothing,
          (Ptr{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqField}),
          x, x, F)
  end
  return a
end

################################################################################
#
#  Ad hoc binary operators
#
################################################################################

function *(x::FqMatrix, y::FqFieldElem)
  z = similar(x)
  for i in 1:nrows(x)
    for j in 1:ncols(x)
      z[i, j] = y * x[i, j]
    end
  end
  return z
end

*(x::FqFieldElem, y::FqMatrix) = y * x

function *(x::FqMatrix, y::ZZRingElem)
  return base_ring(x)(y) * x
end

*(x::ZZRingElem, y::FqMatrix) = y * x

function *(x::FqMatrix, y::Integer)
  return x * base_ring(x)(y)
end

*(x::Integer, y::FqMatrix) = y * x

################################################################################
#
#  Powering
#
################################################################################

# Fall back to generic one

################################################################################
#
#  Row echelon form
#
################################################################################

function rref(a::FqMatrix)
  z = similar(a)
  r = ccall((:fq_default_mat_rref, libflint), Int,
            (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), z, a, base_ring(a))
  return r, z
end

function rref!(a::FqMatrix)
  r = ccall((:fq_default_mat_rref, libflint), Int,
            (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), a, a, base_ring(a))
  return r
end

################################################################################
#
#  Determinant
#
################################################################################

function det(a::FqMatrix)
  !is_square(a) && error("Non-square matrix")
  n = nrows(a)
  R = base_ring(a)
  if n == 0
    return one(R)
  end
  r, p, l, u = lu(a)
  if r < n
    return zero(R)
  else
    d = one(R)
    for i in 1:nrows(u)
      mul!(d, d, u[i, i])
    end
    return (parity(p) == 0 ? d : -d)
  end
end

################################################################################
#
#  Rank
#
################################################################################

function rank(a::FqMatrix)
  n = nrows(a)
  if n == 0
    return 0
  end
  r, _, _, _ = lu(a)
  return r
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(a::FqMatrix)
  !is_square(a) && error("Matrix must be a square matrix")
  z = similar(a)
  r = ccall((:fq_default_mat_inv, libflint), Int,
            (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), z, a, base_ring(a))
  !Bool(r) && error("Matrix not invertible")
  return z
end

################################################################################
#
#  Linear solving
#
################################################################################

Solve.matrix_normal_form_type(::FqField) = Solve.LUTrait()
Solve.matrix_normal_form_type(::FqMatrix) = Solve.LUTrait()

function Solve._can_solve_internal_no_check(::Solve.LUTrait, A::FqMatrix, b::FqMatrix, task::Symbol; side::Symbol = :left)
  if side === :left
    fl, sol, K = Solve._can_solve_internal_no_check(Solve.LUTrait(), transpose(A), transpose(b), task, side = :right)
    return fl, transpose(sol), transpose(K)
  end

  x = similar(A, ncols(A), ncols(b))
  fl = ccall((:fq_default_mat_can_solve, libflint), Cint,
             (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix},
              Ref{FqField}), x, A, b, base_ring(A))
  if task === :only_check || task === :with_solution
    return Bool(fl), x, zero(A, 0, 0)
  end
  return Bool(fl), x, kernel(A, side = :right)
end

# Direct interface to the C functions to be able to write 'generic' code for
# different matrix types
function _solve_tril_right_flint!(x::FqMatrix, L::FqMatrix, B::FqMatrix, unit::Bool)
  ccall((:fq_default_mat_solve_tril, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix}, Cint, Ref{FqField}),
        x, L, B, Cint(unit), base_ring(L))
  return nothing
end

function _solve_triu_right_flint!(x::FqMatrix, U::FqMatrix, B::FqMatrix, unit::Bool)
  ccall((:fq_default_mat_solve_triu, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix}, Cint, Ref{FqField}),
        x, U, B, Cint(unit), base_ring(U))
  return nothing
end

################################################################################
#
#  LU decomposition
#
################################################################################

function lu!(P::Perm, x::FqMatrix)
  P.d .-= 1

  rank = Int(ccall((:fq_default_mat_lu, libflint), Cint,
                   (Ptr{Int}, Ref{FqMatrix}, Cint, Ref{FqField}),
                   P.d, x, 0, base_ring(x)))

  P.d .+= 1

  # flint does x == PLU instead of Px == LU (docs are wrong)
  inv!(P)

  return rank
end

function lu(x::FqMatrix, P = SymmetricGroup(nrows(x)))
  m = nrows(x)
  n = ncols(x)
  P.n != m && error("Permutation does not match matrix")
  p = one(P)
  R = base_ring(x)
  U = deepcopy(x)

  L = similar(x, m, m)

  rank = lu!(p, U)

  for i = 1:m
    for j = 1:n
      if i > j
        L[i, j] = U[i, j]
        U[i, j] = R()
      elseif i == j
        L[i, j] = one(R)
      elseif j <= m
        L[i, j] = R()
      end
    end
  end
  return rank, p, L, U
end

################################################################################
#
#  Windowing
#
################################################################################

function Base.view(x::FqMatrix, r1::Int, c1::Int, r2::Int, c2::Int)

  _checkrange_or_empty(nrows(x), r1, r2) ||
  Base.throw_boundserror(x, (r1:r2, c1:c2))

  _checkrange_or_empty(ncols(x), c1, c2) ||
  Base.throw_boundserror(x, (r1:r2, c1:c2))

  if (r1 > r2)
    r1 = 1
    r2 = 0
  end
  if (c1 > c2)
    c1 = 1
    c2 = 0
  end

  z = FqMatrix()
  z.base_ring = x.base_ring
  z.view_parent = x
  ccall((:fq_default_mat_window_init, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Int, Int, Int, Int, Ref{FqField}),
        z, x, r1 - 1, c1 - 1, r2, c2, base_ring(x))
  finalizer(_fq_default_mat_window_clear_fn, z)
  return z
end

function Base.view(x::FqMatrix, r::AbstractUnitRange{Int}, c::AbstractUnitRange{Int})
  return Base.view(x, first(r), first(c), last(r), last(c))
end

function _fq_default_mat_window_clear_fn(a::FqMatrix)
  ccall((:fq_default_mat_window_clear, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqField}), a, base_ring(a))
end

function sub(x::FqMatrix, r1::Int, c1::Int, r2::Int, c2::Int)
  return deepcopy(Base.view(x, r1, c1, r2, c2))
end

function sub(x::FqMatrix, r::AbstractUnitRange{Int}, c::AbstractUnitRange{Int})
  return deepcopy(Base.view(x, r, c))
end

getindex(x::FqMatrix, r::AbstractUnitRange{Int}, c::AbstractUnitRange{Int}) = sub(x, r, c)

################################################################################
#
#  Concatenation
#
################################################################################

function hcat(x::FqMatrix, y::FqMatrix)
  (base_ring(x) != base_ring(y)) && error("Matrices must have same base ring")
  (nrows(x) != nrows(y)) && error("Matrices must have same number of rows")
  z = similar(x, nrows(x), ncols(x) + ncols(y))
  ccall((:fq_default_mat_concat_horizontal, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix},
         Ref{FqField}),
        z, x, y, base_ring(x))
  return z
end

function vcat(x::FqMatrix, y::FqMatrix)
  (base_ring(x) != base_ring(y)) && error("Matrices must have same base ring")
  (ncols(x) != ncols(y)) && error("Matrices must have same number of columns")
  z = similar(x, nrows(x) + nrows(y), ncols(x))
  ccall((:fq_default_mat_concat_vertical, libflint), Nothing,
        (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqMatrix},
         Ref{FqField}),
        z, x, y, base_ring(x))
  return z
end

################################################################################
#
#  Characteristic polynomial
#
################################################################################

function charpoly(R::FqPolyRing, a::FqMatrix)
  !is_square(a) && error("Matrix must be square")
  base_ring(R) != base_ring(a) && error("Must have common base ring")
  p = R()
  ccall((:fq_default_mat_charpoly, libflint), Nothing,
        (Ref{FqPolyRingElem}, Ref{FqMatrix}, Ref{FqField}), p, a, base_ring(a))
  return p
end

function charpoly_danivlesky!(R::FqPolyRing, a::FqMatrix)
  !is_square(a) && error("Matrix must be square")
  base_ring(R) != base_ring(a) && error("Must have common base ring")
  p = R()
  ccall((:fq_default_mat_charpoly_danilevsky, libflint), Nothing,
        (Ref{FqPolyRingElem}, Ref{FqMatrix}, Ref{FqField}), p, a, base_ring(a))
  return p
end


################################################################################
#
#  Minimal polynomial
#
################################################################################

function minpoly(R::FqPolyRing, a::FqMatrix)
  !is_square(a) && error("Matrix must be square")
  base_ring(R) != base_ring(a) && error("Must have common base ring")
  m = deepcopy(a)
  p = R()
  ccall((:fq_default_mat_minpoly, libflint), Nothing,
        (Ref{FqPolyRingElem}, Ref{FqMatrix}, Ref{FqField}), p, m, base_ring(a))
  return p
end

###############################################################################
#
#   Promotion rules
#
###############################################################################

promote_rule(::Type{FqMatrix}, ::Type{V}) where {V <: Integer} = FqMatrix

promote_rule(::Type{FqMatrix}, ::Type{FqFieldElem}) = FqMatrix

promote_rule(::Type{FqMatrix}, ::Type{ZZRingElem}) = FqMatrix

################################################################################
#
#  Parent object overloading
#
################################################################################

function (a::FqMatrixSpace)()
  z = FqMatrix(nrows(a), ncols(a), base_ring(a))
  return z
end

function (a::FqMatrixSpace)(b::FqFieldElem)
  parent(b) != base_ring(a) && error("Unable to coerce to matrix")
  return FqMatrix(nrows(a), ncols(a), b)
end

function (a::FqMatrixSpace)(arr::AbstractMatrix{<:IntegerUnion})
  _check_dim(nrows(a), ncols(a), arr)
  return FqMatrix(arr, base_ring(a))
end

function (a::FqMatrixSpace)(arr::AbstractVector{<:IntegerUnion})
  _check_dim(nrows(a), ncols(a), arr)
  return FqMatrix(nrows(a), ncols(a), arr, base_ring(a))
end

function (a::FqMatrixSpace)(arr::AbstractMatrix{FqFieldElem})
  _check_dim(nrows(a), ncols(a), arr)
  (length(arr) > 0 && (base_ring(a) != parent(arr[1]))) && error("Elements must have same base ring")
  return FqMatrix(arr, base_ring(a))
end

function (a::FqMatrixSpace)(arr::AbstractVector{FqFieldElem})
  _check_dim(nrows(a), ncols(a), arr)
  (length(arr) > 0 && (base_ring(a) != parent(arr[1]))) && error("Elements must have same base ring")
  return FqMatrix(nrows(a), ncols(a), arr, base_ring(a))
end

function (a::FqMatrixSpace)(b::ZZMatrix)
  (ncols(a) != ncols(b) || nrows(a) != nrows(b)) && error("Dimensions do not fit")
  return FqMatrix(b, base_ring(a))
end

function (a::FqMatrixSpace)(b::Union{zzModMatrix, fpMatrix})
  characteristic(base_ring(b)) != characteristic(base_ring(a)) &&
  error("Incompatible characteristic")
  (ncols(a) != ncols(b) || nrows(a) != nrows(b)) && error("Dimensions do not fit")
  return FqMatrix(b, base_ring(a))
end

function (a::FqMatrixSpace)(b::Zmod_fmpz_mat)
  characteristic(base_ring(b)) != characteristic(base_ring(a)) &&
  error("Incompatible characteristic")
  (ncols(a) != ncols(b) || nrows(a) != nrows(b)) && error("Dimensions do not fit")
  return FqMatrix(b, base_ring(a))
end

###############################################################################
#
#   Matrix constructor
#
###############################################################################

function matrix(R::FqField, arr::AbstractMatrix{<: Union{FqFieldElem, ZZRingElem, Integer}})
  Base.require_one_based_indexing(arr)
  z = FqMatrix(arr, R)
  return z
end

function matrix(R::FqField, r::Int, c::Int, arr::AbstractVector{<: Union{FqFieldElem, ZZRingElem, Integer}})
  _check_dim(r, c, arr)
  z = FqMatrix(r, c, arr, R)
  return z
end

###############################################################################
#
#  Zero matrix
#
###############################################################################

function zero_matrix(R::FqField, r::Int, c::Int)
  if r < 0 || c < 0
    error("dimensions must not be negative")
  end
  z = FqMatrix(r, c, R)
  return z
end

################################################################################
#
#  Entry pointers
#
################################################################################

function fq_default_mat_entry_ptr(a::FqMatrix, i, j)
  t = _fq_default_ctx_type(base_ring(a))
  ptr = pointer_from_objref(a)
  if t == _FQ_DEFAULT_FQ_ZECH
    pptr = ccall((:fq_zech_mat_entry, libflint), Ptr{FqFieldElem},
                 (Ptr{Cvoid}, Int, Int), ptr, i - 1, j - 1)
  elseif t == _FQ_DEFAULT_FQ_NMOD
    pptr = ccall((:fq_nmod_mat_entry, libflint), Ptr{FqFieldElem},
                 (Ptr{Cvoid}, Int, Int), ptr, i - 1, j - 1)
  elseif t == _FQ_DEFAULT_FQ
    pptr = ccall((:fq_mat_entry, libflint), Ptr{FqFieldElem},
                 (Ptr{Cvoid}, Int, Int), ptr, i - 1, j - 1)
  elseif t == _FQ_DEFAULT_NMOD
    pptr = ccall((:nmod_mat_entry_ptr, libflint), Ptr{FqFieldElem},
                 (Ptr{Cvoid}, Int, Int), ptr, i - 1, j - 1)
  else#if t == _FQ_DEFAULT_FMPZ_NMOD
    pptr = ccall((:fmpz_mod_mat_entry, libflint), Ptr{FqFieldElem},
                 (Ptr{Cvoid}, Int, Int), ptr, i - 1, j - 1)
  end
  return pptr
end

################################################################################
#
#  Kernel
#
################################################################################

function nullspace(M::FqMatrix)
  N = similar(M, ncols(M), ncols(M))
  nullity = ccall((:fq_default_mat_nullspace, libflint), Int,
                  (Ref{FqMatrix}, Ref{FqMatrix}, Ref{FqField}), N, M, base_ring(M))
  return nullity, view(N, 1:nrows(N), 1:nullity)
end
