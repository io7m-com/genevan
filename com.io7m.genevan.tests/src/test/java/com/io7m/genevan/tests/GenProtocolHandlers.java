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

package com.io7m.genevan.tests;

import com.io7m.genevan.core.GenProtocolHandlerType;
import com.io7m.genevan.core.GenProtocolIdentifier;
import com.io7m.genevan.core.GenProtocolVersion;

import java.math.BigInteger;
import java.util.Objects;

/**
 * Convenience functions to construct test protocol handlers.
 */

public final class GenProtocolHandlers
{
  private GenProtocolHandlers()
  {

  }

  /**
   * @return A handler with the exact identifier
   */

  public static GenProtocolHandlerType exact(
    final GenProtocolIdentifier identifier)
  {
    return new Exact(identifier);
  }

  /**
   * @return A handler with the exact identifier values
   */

  public static GenProtocolHandlerType exact(
    final String id,
    final int major,
    final int minor)
  {
    return new Exact(new GenProtocolIdentifier(id,
                                               new GenProtocolVersion(BigInteger.valueOf(
                                                 (long) major),
                                                                      BigInteger.valueOf(
                                                                        (long) minor))));
  }

  private static final class Exact implements GenProtocolHandlerType
  {
    private final GenProtocolIdentifier supports;

    Exact(
      final GenProtocolIdentifier inSupports)
    {
      this.supports = Objects.requireNonNull(inSupports, "supports");
    }

    @Override
    public boolean equals(final Object o)
    {
      if (this == o) {
        return true;
      }
      if (o == null || !this.getClass().equals(o.getClass())) {
        return false;
      }
      final Exact exact = (Exact) o;
      return this.supports.equals(exact.supports);
    }

    @Override
    public int hashCode()
    {
      return Objects.hash(this.supports);
    }

    @Override
    public String toString()
    {
      return "[Exact %s]".formatted(this.supports);
    }

    @Override
    public GenProtocolIdentifier supported()
    {
      return this.supports;
    }
  }
}
