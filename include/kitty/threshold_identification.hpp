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
//enum Constraint_Type { GE=1, LE, EQ }; //GE=1 /* >=      <=  == */
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
  auto count = 0; // count the number of variables with respect to which the function is binate
  bool unate;
  for ( auto i = 0u; i < numvars; i++ )
  {
    unate = true;
    auto const tt1 = cofactor0( tt, i );
    auto const tt2 = cofactor1( tt, i );
    for ( auto bit = 0; bit < ( 2 << ( numvars - 1 ) ); bit++ )
    {
      if ( get_bit( tt1, bit ) >= get_bit( tt2, bit ) ) //negative unateness check
      {
        continue;
      }
      else
      {
        unate = false;
      }
    }
    if(unate == false){
    unate =true;
    for ( auto bit = 0; bit < ( 2 << ( numvars - 1 ) ); bit++ )
    {
      if ( get_bit( tt1, bit ) <= get_bit( tt2, bit ) ) //positive unateness check
      {
        continue;
      }
      else
      {
        unate = false;
      }
    }
   if (unate == false) count++;
  }
  }
  if( count == numvars) //if it is binate with respect to all functions
    return true;
  else
    return false;
}
void convert_to_binary(int64_t num,std::vector<char> bin_num, uint32_t _num_vars)
{
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
  std::reverse(bin_num.begin(),bin_num.end())
  return;
}
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  /* TODO */
  std::vector<int64_t> ONSET, OFFSET;
  /* if tt is non-TF: */
  if(is_binate) {// a function is binate in any variable, it is surely non-TF
     return false;
  }
  /*otherwise tt could be TF*/
   for ( auto bit = tt.numvars - 1; bit > 0; bit-- )
    {
      if(get_bit( tt, bit ) == 1){ //then add it to the ONSET
          ONSET.emplace_back(bit);
      }
      else{ //else add it to the OFFSET
         OFFSET.emplace_back(bit);
      }
    }
    //NOT CORRECT
 /* for ( auto i = 0u; i < tt.num_vars(); i++ )
  {
    if(is_negative_unate_in_x(tt,i)){
      //change x_i with bar(x_i) <=> exchanging ONSET with the OFFSET
    ONSET(i)=swap(OFFSET(i));
    }
  }*/
   lprec *plp;
   REAL row[tt.num_vars()+2];
   plp=make_lp(0,num_vars()+1);
   if(plp == NULL){
      return false; //couldn't construct a new model
   }
   set_add_rowmode(lp,TRUE);
   std::vector<char> binary;
   /*ONSET CONSTRAINTS*/
   for(auto i = 1u; i <= ONSET.size(); ++i){
      convert_to_binary(ONSET(i),binary,tt.num_vars());
      for ( auto k = 0u; k < tt.num_vars(); k++ ){
        if(is_negative_unate_in_x(tt,k)){
           if(binary(k) == 0) binary(k)=1;
           else binary(k)=0;
        }
      }
      for(auto j = 1u; j <= binary.size(); ++j){
           row[j]= REAL(binary(j));
        }
      row[j]=-1.0;
      add_constraint(plp,row,GE,0);
   }
   /*OFFSET CONSTRAINTS*/
   for(auto i = 1u; i <= ONSET.size(); ++i){
      convert_to_binary(ONSET(i),binary,tt.num_vars());
      for ( auto k = 0u; k < tt.num_vars(); k++ ){
        if(is_negative_unate_in_x(tt,k)){
           if(binary(k) == 0) binary(k)=1;
           else binary(k)=0;
        }
      }
      for(auto j = 1u; j <= binary.size(); ++j){
           row[j]= REAL(binary(j));
        }
      row[j]=-1.0;
      add_constraint(plp,row,LE,-1.0);
   }
   set_add_rowmode(plp, FALSE);
   /*SET OBJECTIVE FUNCTION*/
   for(auto i = 1u; i <= (ONSET.size()+1); ++i){
     row[i]=1.0;
   }
   set_obj_fn(lp, row);
   /*SOLVE LP*/
   set_minim(lp);
   print_lp(plp);
  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  if ( plf )
  {
    *plf = linear_form;
  }
  delete_lp(plp);
  return true;
}

} /* namespace kitty */
