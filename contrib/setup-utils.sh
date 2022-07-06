#!/usr/bin/env bash

# this file is taken and modified from Boolector

die () {
  echo "*** error: $*" 1>&2
  exit 1
}

[ ! -e efmc/sts.py ] && die "$0 not called from efmc base directory"

DEPS_DIR="$(pwd)/deps"
INSTALL_DIR="${DEPS_DIR}/install"
INSTALL_LIB_DIR="${INSTALL_DIR}/lib"
INSTALL_INCLUDE_DIR="${INSTALL_DIR}/include"
INSTALL_BIN_DIR="${INSTALL_DIR}/bin"

if type nproc > /dev/null 2>&1; then
  NPROC=$(nproc)
elif [ "$(uname -s)" == "Darwin" ]; then
  NPROC=$(sysctl -n hw.physicalcpu)
else
  NPROC=2
fi


mkdir -p "${DEPS_DIR}"
mkdir -p "${INSTALL_LIB_DIR}"
mkdir -p "${INSTALL_INCLUDE_DIR}"
mkdir -p "${INSTALL_BIN_DIR}"

function install_lib
{
  cp "$1" "${INSTALL_DIR}/lib"
}

function install_include
{
  include="$1"
  subdir="$2"
  if [ -n "$subdir" ]; then
    mkdir -p "${INSTALL_INCLUDE_DIR}/$subdir"
  fi
  cp "$include" "${INSTALL_INCLUDE_DIR}/$subdir"
}

function install_bin
{
  cp "$1" "${INSTALL_BIN_DIR}"
}

function is_windows
{
  #
  # Helper function to check if we're running under Windows, returns false
  # otherwise.
  #
  case "$(uname -s)" in
    CYGWIN*|MINGW32*|MINGW64*|MSYS*)
      return
      ;;
  esac
  false
}

function is_windows
{
  #
  # Helper function to check if we're running under Windows, returns false
  # otherwise.
  #
  case "$(uname -s)" in
    CYGWIN*|MINGW32*|MINGW64*|MSYS*)
      return
      ;;
  esac
  false
}

function download_github
{
  local repo="$1"
  local version="$2"
  local location="$3"
  local tar_args="$4"
  local name=$(echo "$repo" | cut -d '/' -f 2)
  local archive="$name-$version.tar.gz"

  curl -o "$archive" -L "https://github.com/$repo/archive/$version.tar.gz"

  rm -rf "${location}"
  tar xfvz "$archive" $tar_args
  rm "$archive"
  mv "$name-$version" "${location}"
}