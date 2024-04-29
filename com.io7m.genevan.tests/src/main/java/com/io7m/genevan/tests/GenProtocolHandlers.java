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

import com.io7m.genevan.core.GenProtocolClientHandlerType;
import com.io7m.genevan.core.GenProtocolIdentifier;
import com.io7m.genevan.core.GenProtocolServerEndpointType;
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

  public static GenProtocolClientHandlerType exactClient(
    final GenProtocolIdentifier identifier)
  {
    return new ExactClient(identifier);
  }

  /**
   * @return A handler with the exact identifier values
   */

  public static GenProtocolClientHandlerType exactClient(
    final String id,
    final int major,
    final int minor)
  {
    final var version =
      new GenProtocolVersion(
        BigInteger.valueOf((long) major),
        BigInteger.valueOf((long) minor)
      );
    return new ExactClient(new GenProtocolIdentifier(id, version));
  }

  /**
   * @return A handler with the exact identifier
   */

  public static GenProtocolServerEndpointType exactServer(
    final GenProtocolIdentifier identifier)
  {
    return new ExactServer(identifier);
  }

  /**
   * @return A handler with the exact identifier values
   */

  public static GenProtocolServerEndpointType exactServer(
    final String id,
    final int major,
    final int minor)
  {
    final var version =
      new GenProtocolVersion(
        BigInteger.valueOf((long) major),
        BigInteger.valueOf((long) minor)
      );
    return new ExactServer(new GenProtocolIdentifier(id, version));
  }

  private static final class ExactClient
    implements GenProtocolClientHandlerType
  {
    private final GenProtocolIdentifier supports;

    ExactClient(
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
      final ExactClient exact = (ExactClient) o;
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
      return "[ExactClient %s]".formatted(this.supports);
    }

    @Override
    public GenProtocolIdentifier supported()
    {
      return this.supports;
    }
  }

  private static final class ExactServer
    implements GenProtocolServerEndpointType
  {
    private final GenProtocolIdentifier supports;

    ExactServer(
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
      final ExactServer exact = (ExactServer) o;
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
      return "[ExactServer %s]".formatted(this.supports);
    }

    @Override
    public GenProtocolIdentifier supported()
    {
      return this.supports;
    }
  }
}
