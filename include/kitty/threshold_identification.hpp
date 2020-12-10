/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include "lpsolve/lp_lib.h" /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "operations.hpp"
#include "cube.hpp"
#include "algorithm.hpp"


namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_positive_unate_in_x( const TT& tt, const uint8_t x ) //check if the function is positive unate in the variable x
{
    auto numvars = tt.num_vars();
    auto const tt1 = cofactor0( tt, x );
    auto const tt2 = cofactor1( tt, x );
    for ( auto bit = 0; bit < ( 2 << ( numvars - 1 ) ); bit++ )
    {
      if ( get_bit( tt1, bit ) <= get_bit( tt2, bit ) )
      {
        continue;
      }
      else
      {
        return false;
      }
    }
  return true;
}
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_negative_unate_in_x( const TT& tt, const uint8_t x ) //check if the function is negative unate in the variable x
{
    auto numvars = tt.num_vars();
    auto const tt1 = cofactor0( tt, x );
    auto const tt2 = cofactor1( tt, x );
    for ( auto bit = 0; bit < ( 2 << ( numvars - 1 ) ); bit++ )
    {
      if ( get_bit( tt1, bit ) >= get_bit( tt2, bit ) )
      {
        continue;
      }
      else
      {
        return false;
      }
    }
  return true;
}
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_binate( const TT& tt ) //if the function is binate in any variable returns true
{
  auto numvars = tt.num_vars();
  for ( auto i = 0u; i < numvars; i++ )
  {
    if(!(is_negative_unate_in_x(tt,i) || is_positive_unate_in_x(tt,i)))
      return true;
  }
    return false;
}
std::vector<char> convert_to_binary(int64_t num, uint32_t num_vars)
{
  std::vector<char> bin_num;
  uint32_t i=0;
  while(num!=0){
    bin_num.emplace_back(num%2);
    num=num/2;
    i++;
  }
  while(i!= num_vars){
    i++;
    bin_num.emplace_back(0);
  }
  return bin_num;
}
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  std::vector<char> binary;
  /* if tt is non-TF: */
  if(is_binate(tt)) {// a function is binate in any variable, it is surely non-TF
     return false;
  }
  /*otherwise tt could be TF*/
   lprec *plp;
   REAL *row= nullptr;
   row = (REAL *) malloc((tt.num_vars()+2) * sizeof(*row));
   plp=make_lp(0,tt.num_vars()+1);
   if(plp == NULL){
      return false; //couldn't construct a new model
   }
   set_add_rowmode(plp,TRUE);
  /*CONSTRAINTS*/
   int64_t l=0;
  for(uint64_t i = tt.num_bits(); i > 0; i--){
    binary=convert_to_binary(int64_t (l),tt.num_vars());
    for ( auto k = 0u; k < tt.num_vars(); k++ )
    {
      if ( is_negative_unate_in_x( tt, k ) )
      {
        if ( binary[k] == 0 )
          binary[k] = 1;
        else
          binary[k] = 0;
      }
    }
      for ( auto j = 0u; j < binary.size(); ++j )
      {
        row[j + 1] = REAL( binary[j] );
      }
      row[binary.size() + 1] = -1.0;
      if(get_bit(tt,l)==1)
      {
        add_constraint( plp, row, GE, 0 );
      }
      else{
        add_constraint(plp,row,LE,-1.0);
      }
    l++;
    }
   /*GREATER THAN 0 CONSTRAINTS*/
  for ( auto i = 0u; i < tt.num_vars()+1; i++ ){
    for ( auto j = 0u; j <= tt.num_vars()+1; j++ ){
      row[j] = 0;
    }
     row[i+1] = 1.0;
     add_constraint(plp,row,GE,0);
  }
   set_add_rowmode(plp, FALSE);
   /*SET OBJECTIVE FUNCTION*/
   for(auto i = 1u; i <= (tt.num_vars()+1); ++i){
     row[i]=1.0;
   }
   set_obj_fn(plp, row);
   /*PRINT LP*/
   print_lp(plp);
   /*SOLVE LP*/
   set_minim(plp);
   /*SET INTEGERS*/
  for(auto i = 1u; i <= (tt.num_vars()+1); ++i){
    set_int(plp,i,TRUE);
  }
   auto ret=solve(plp);
   if(ret==2)
   { //the model is infeasible hence the function is non-TF
     return false;
   }
  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  REAL *sol= nullptr;
  sol = (REAL *) malloc((tt.num_vars()+1) * sizeof(*sol));
  get_variables(plp, sol);
  for(auto i=0u; i<(1+tt.num_vars()) ;i++){
     linear_form.push_back(int64_t(sol[i]));
   }
  for ( auto k = 0u; k < tt.num_vars(); k++ )
   {
     if ( is_negative_unate_in_x( tt, k ) )
     {
       linear_form[k] = -linear_form[k];
       linear_form[linear_form.size() - 1] = linear_form[linear_form.size() - 1] + linear_form[k];
     }
   }
  if ( plf )
  {
    *plf = linear_form;
  }
  /*RELEASE MEMORY ALLOCATION*/
  if(row != NULL)
    free(row);
  if(sol != NULL)
    free(sol);
  delete_lp(plp);
  return true;
}
} /* namespace kitty */
