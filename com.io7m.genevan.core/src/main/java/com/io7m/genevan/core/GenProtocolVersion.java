/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

package com.io7m.genevan.core;

import java.math.BigInteger;
import java.util.Comparator;
import java.util.Objects;

/**
 * The version number of a semantically-versioned protocol.
 *
 * @param versionMajor The major version of the protocol
 * @param versionMinor The minor version of the protocol
 */

public record GenProtocolVersion(
  BigInteger versionMajor,
  BigInteger versionMinor)
  implements Comparable<GenProtocolVersion>
{
  /**
   * The version number of a semantically-versioned protocol.
   *
   * @param versionMajor The major version of the protocol
   * @param versionMinor The minor version of the protocol
   */

  public GenProtocolVersion
  {
    Objects.requireNonNull(versionMajor, "versionMajor");
    Objects.requireNonNull(versionMinor, "versionMinor");

    if (versionMajor.compareTo(BigInteger.ZERO) < 0) {
      throw new IllegalArgumentException(
        "Major version number %s must be non-negative".formatted(versionMajor)
      );
    }
    if (versionMinor.compareTo(BigInteger.ZERO) < 0) {
      throw new IllegalArgumentException(
        "Minor version number %s must be non-negative".formatted(versionMinor)
      );
    }
  }

  /**
   * @param other The other version
   *
   * @return {@code true} if this version is compatible with the other version
   */

  public boolean isCompatibleWith(
    final GenProtocolVersion other)
  {
    Objects.requireNonNull(other, "other");
    return Objects.equals(this.versionMajor, other.versionMajor);
  }

  @Override
  public int compareTo(
    final GenProtocolVersion other)
  {
    return Comparator.comparing(GenProtocolVersion::versionMajor)
      .thenComparing(GenProtocolVersion::versionMinor)
      .compare(this, other);
  }
}
